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
Require Import p125_split_words.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function decimal_len -----*)

Definition decimal_len_safety_wit_1 :=
forall (value_pre: Z) (PreH1 : (0 <= value_pre)) (PreH2 : (value_pre < INT_MAX)) ,
  ((( &( "value" ) )) # Int  |-> value_pre)
|--
  “ (1000000000 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1000000000) ”
.

Definition decimal_len_safety_wit_2 :=
forall (value_pre: Z) (PreH1 : (value_pre >= 1000000000)) (PreH2 : (0 <= value_pre)) (PreH3 : (value_pre < INT_MAX)) ,
  ((( &( "value" ) )) # Int  |-> value_pre)
|--
  “ (10 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 10) ”
.

Definition decimal_len_safety_wit_3 :=
forall (value_pre: Z) (PreH1 : (value_pre < 1000000000)) (PreH2 : (0 <= value_pre)) (PreH3 : (value_pre < INT_MAX)) ,
  ((( &( "value" ) )) # Int  |-> value_pre)
|--
  “ (100000000 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 100000000) ”
.

Definition decimal_len_safety_wit_4 :=
forall (value_pre: Z) (PreH1 : (value_pre >= 100000000)) (PreH2 : (value_pre < 1000000000)) (PreH3 : (0 <= value_pre)) (PreH4 : (value_pre < INT_MAX)) ,
  ((( &( "value" ) )) # Int  |-> value_pre)
|--
  “ (9 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 9) ”
.

Definition decimal_len_safety_wit_5 :=
forall (value_pre: Z) (PreH1 : (value_pre < 100000000)) (PreH2 : (value_pre < 1000000000)) (PreH3 : (0 <= value_pre)) (PreH4 : (value_pre < INT_MAX)) ,
  ((( &( "value" ) )) # Int  |-> value_pre)
|--
  “ (10000000 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 10000000) ”
.

Definition decimal_len_safety_wit_6 :=
forall (value_pre: Z) (PreH1 : (value_pre >= 10000000)) (PreH2 : (value_pre < 100000000)) (PreH3 : (value_pre < 1000000000)) (PreH4 : (0 <= value_pre)) (PreH5 : (value_pre < INT_MAX)) ,
  ((( &( "value" ) )) # Int  |-> value_pre)
|--
  “ (8 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 8) ”
.

Definition decimal_len_safety_wit_7 :=
forall (value_pre: Z) (PreH1 : (value_pre < 10000000)) (PreH2 : (value_pre < 100000000)) (PreH3 : (value_pre < 1000000000)) (PreH4 : (0 <= value_pre)) (PreH5 : (value_pre < INT_MAX)) ,
  ((( &( "value" ) )) # Int  |-> value_pre)
|--
  “ (1000000 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1000000) ”
.

Definition decimal_len_safety_wit_8 :=
forall (value_pre: Z) (PreH1 : (value_pre >= 1000000)) (PreH2 : (value_pre < 10000000)) (PreH3 : (value_pre < 100000000)) (PreH4 : (value_pre < 1000000000)) (PreH5 : (0 <= value_pre)) (PreH6 : (value_pre < INT_MAX)) ,
  ((( &( "value" ) )) # Int  |-> value_pre)
|--
  “ (7 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 7) ”
.

Definition decimal_len_safety_wit_9 :=
forall (value_pre: Z) (PreH1 : (value_pre < 1000000)) (PreH2 : (value_pre < 10000000)) (PreH3 : (value_pre < 100000000)) (PreH4 : (value_pre < 1000000000)) (PreH5 : (0 <= value_pre)) (PreH6 : (value_pre < INT_MAX)) ,
  ((( &( "value" ) )) # Int  |-> value_pre)
|--
  “ (100000 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 100000) ”
.

Definition decimal_len_safety_wit_10 :=
forall (value_pre: Z) (PreH1 : (value_pre >= 100000)) (PreH2 : (value_pre < 1000000)) (PreH3 : (value_pre < 10000000)) (PreH4 : (value_pre < 100000000)) (PreH5 : (value_pre < 1000000000)) (PreH6 : (0 <= value_pre)) (PreH7 : (value_pre < INT_MAX)) ,
  ((( &( "value" ) )) # Int  |-> value_pre)
|--
  “ (6 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 6) ”
.

Definition decimal_len_safety_wit_11 :=
forall (value_pre: Z) (PreH1 : (value_pre < 100000)) (PreH2 : (value_pre < 1000000)) (PreH3 : (value_pre < 10000000)) (PreH4 : (value_pre < 100000000)) (PreH5 : (value_pre < 1000000000)) (PreH6 : (0 <= value_pre)) (PreH7 : (value_pre < INT_MAX)) ,
  ((( &( "value" ) )) # Int  |-> value_pre)
|--
  “ (10000 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 10000) ”
.

Definition decimal_len_safety_wit_12 :=
forall (value_pre: Z) (PreH1 : (value_pre >= 10000)) (PreH2 : (value_pre < 100000)) (PreH3 : (value_pre < 1000000)) (PreH4 : (value_pre < 10000000)) (PreH5 : (value_pre < 100000000)) (PreH6 : (value_pre < 1000000000)) (PreH7 : (0 <= value_pre)) (PreH8 : (value_pre < INT_MAX)) ,
  ((( &( "value" ) )) # Int  |-> value_pre)
|--
  “ (5 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 5) ”
.

Definition decimal_len_safety_wit_13 :=
forall (value_pre: Z) (PreH1 : (value_pre < 10000)) (PreH2 : (value_pre < 100000)) (PreH3 : (value_pre < 1000000)) (PreH4 : (value_pre < 10000000)) (PreH5 : (value_pre < 100000000)) (PreH6 : (value_pre < 1000000000)) (PreH7 : (0 <= value_pre)) (PreH8 : (value_pre < INT_MAX)) ,
  ((( &( "value" ) )) # Int  |-> value_pre)
|--
  “ (1000 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1000) ”
.

Definition decimal_len_safety_wit_14 :=
forall (value_pre: Z) (PreH1 : (value_pre >= 1000)) (PreH2 : (value_pre < 10000)) (PreH3 : (value_pre < 100000)) (PreH4 : (value_pre < 1000000)) (PreH5 : (value_pre < 10000000)) (PreH6 : (value_pre < 100000000)) (PreH7 : (value_pre < 1000000000)) (PreH8 : (0 <= value_pre)) (PreH9 : (value_pre < INT_MAX)) ,
  ((( &( "value" ) )) # Int  |-> value_pre)
|--
  “ (4 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 4) ”
.

Definition decimal_len_safety_wit_15 :=
forall (value_pre: Z) (PreH1 : (value_pre < 1000)) (PreH2 : (value_pre < 10000)) (PreH3 : (value_pre < 100000)) (PreH4 : (value_pre < 1000000)) (PreH5 : (value_pre < 10000000)) (PreH6 : (value_pre < 100000000)) (PreH7 : (value_pre < 1000000000)) (PreH8 : (0 <= value_pre)) (PreH9 : (value_pre < INT_MAX)) ,
  ((( &( "value" ) )) # Int  |-> value_pre)
|--
  “ (100 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 100) ”
.

Definition decimal_len_safety_wit_16 :=
forall (value_pre: Z) (PreH1 : (value_pre >= 100)) (PreH2 : (value_pre < 1000)) (PreH3 : (value_pre < 10000)) (PreH4 : (value_pre < 100000)) (PreH5 : (value_pre < 1000000)) (PreH6 : (value_pre < 10000000)) (PreH7 : (value_pre < 100000000)) (PreH8 : (value_pre < 1000000000)) (PreH9 : (0 <= value_pre)) (PreH10 : (value_pre < INT_MAX)) ,
  ((( &( "value" ) )) # Int  |-> value_pre)
|--
  “ (3 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 3) ”
.

Definition decimal_len_safety_wit_17 :=
forall (value_pre: Z) (PreH1 : (value_pre < 100)) (PreH2 : (value_pre < 1000)) (PreH3 : (value_pre < 10000)) (PreH4 : (value_pre < 100000)) (PreH5 : (value_pre < 1000000)) (PreH6 : (value_pre < 10000000)) (PreH7 : (value_pre < 100000000)) (PreH8 : (value_pre < 1000000000)) (PreH9 : (0 <= value_pre)) (PreH10 : (value_pre < INT_MAX)) ,
  ((( &( "value" ) )) # Int  |-> value_pre)
|--
  “ (10 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 10) ”
.

Definition decimal_len_safety_wit_18 :=
forall (value_pre: Z) (PreH1 : (value_pre >= 10)) (PreH2 : (value_pre < 100)) (PreH3 : (value_pre < 1000)) (PreH4 : (value_pre < 10000)) (PreH5 : (value_pre < 100000)) (PreH6 : (value_pre < 1000000)) (PreH7 : (value_pre < 10000000)) (PreH8 : (value_pre < 100000000)) (PreH9 : (value_pre < 1000000000)) (PreH10 : (0 <= value_pre)) (PreH11 : (value_pre < INT_MAX)) ,
  ((( &( "value" ) )) # Int  |-> value_pre)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition decimal_len_safety_wit_19 :=
forall (value_pre: Z) (PreH1 : (value_pre < 10)) (PreH2 : (value_pre < 100)) (PreH3 : (value_pre < 1000)) (PreH4 : (value_pre < 10000)) (PreH5 : (value_pre < 100000)) (PreH6 : (value_pre < 1000000)) (PreH7 : (value_pre < 10000000)) (PreH8 : (value_pre < 100000000)) (PreH9 : (value_pre < 1000000000)) (PreH10 : (0 <= value_pre)) (PreH11 : (value_pre < INT_MAX)) ,
  ((( &( "value" ) )) # Int  |-> value_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition decimal_len_return_wit_1 :=
forall (value_pre: Z) (PreH1 : (value_pre < 10)) (PreH2 : (value_pre < 100)) (PreH3 : (value_pre < 1000)) (PreH4 : (value_pre < 10000)) (PreH5 : (value_pre < 100000)) (PreH6 : (value_pre < 1000000)) (PreH7 : (value_pre < 10000000)) (PreH8 : (value_pre < 100000000)) (PreH9 : (value_pre < 1000000000)) (PreH10 : (0 <= value_pre)) (PreH11 : (value_pre < INT_MAX)) ,
  TT && emp
|--
  “ (1 <= 1) ”
  &&  “ (1 < INT_MAX) ”
  &&  emp
.

Definition decimal_len_return_wit_2 :=
forall (value_pre: Z) (PreH1 : (value_pre >= 10)) (PreH2 : (value_pre < 100)) (PreH3 : (value_pre < 1000)) (PreH4 : (value_pre < 10000)) (PreH5 : (value_pre < 100000)) (PreH6 : (value_pre < 1000000)) (PreH7 : (value_pre < 10000000)) (PreH8 : (value_pre < 100000000)) (PreH9 : (value_pre < 1000000000)) (PreH10 : (0 <= value_pre)) (PreH11 : (value_pre < INT_MAX)) ,
  TT && emp
|--
  “ (1 <= 2) ”
  &&  “ (2 < INT_MAX) ”
  &&  emp
.

Definition decimal_len_return_wit_3 :=
forall (value_pre: Z) (PreH1 : (value_pre >= 100)) (PreH2 : (value_pre < 1000)) (PreH3 : (value_pre < 10000)) (PreH4 : (value_pre < 100000)) (PreH5 : (value_pre < 1000000)) (PreH6 : (value_pre < 10000000)) (PreH7 : (value_pre < 100000000)) (PreH8 : (value_pre < 1000000000)) (PreH9 : (0 <= value_pre)) (PreH10 : (value_pre < INT_MAX)) ,
  TT && emp
|--
  “ (1 <= 3) ”
  &&  “ (3 < INT_MAX) ”
  &&  emp
.

Definition decimal_len_return_wit_4 :=
forall (value_pre: Z) (PreH1 : (value_pre >= 1000)) (PreH2 : (value_pre < 10000)) (PreH3 : (value_pre < 100000)) (PreH4 : (value_pre < 1000000)) (PreH5 : (value_pre < 10000000)) (PreH6 : (value_pre < 100000000)) (PreH7 : (value_pre < 1000000000)) (PreH8 : (0 <= value_pre)) (PreH9 : (value_pre < INT_MAX)) ,
  TT && emp
|--
  “ (1 <= 4) ”
  &&  “ (4 < INT_MAX) ”
  &&  emp
.

Definition decimal_len_return_wit_5 :=
forall (value_pre: Z) (PreH1 : (value_pre >= 10000)) (PreH2 : (value_pre < 100000)) (PreH3 : (value_pre < 1000000)) (PreH4 : (value_pre < 10000000)) (PreH5 : (value_pre < 100000000)) (PreH6 : (value_pre < 1000000000)) (PreH7 : (0 <= value_pre)) (PreH8 : (value_pre < INT_MAX)) ,
  TT && emp
|--
  “ (1 <= 5) ”
  &&  “ (5 < INT_MAX) ”
  &&  emp
.

Definition decimal_len_return_wit_6 :=
forall (value_pre: Z) (PreH1 : (value_pre >= 100000)) (PreH2 : (value_pre < 1000000)) (PreH3 : (value_pre < 10000000)) (PreH4 : (value_pre < 100000000)) (PreH5 : (value_pre < 1000000000)) (PreH6 : (0 <= value_pre)) (PreH7 : (value_pre < INT_MAX)) ,
  TT && emp
|--
  “ (1 <= 6) ”
  &&  “ (6 < INT_MAX) ”
  &&  emp
.

Definition decimal_len_return_wit_7 :=
forall (value_pre: Z) (PreH1 : (value_pre >= 1000000)) (PreH2 : (value_pre < 10000000)) (PreH3 : (value_pre < 100000000)) (PreH4 : (value_pre < 1000000000)) (PreH5 : (0 <= value_pre)) (PreH6 : (value_pre < INT_MAX)) ,
  TT && emp
|--
  “ (1 <= 7) ”
  &&  “ (7 < INT_MAX) ”
  &&  emp
.

Definition decimal_len_return_wit_8 :=
forall (value_pre: Z) (PreH1 : (value_pre >= 10000000)) (PreH2 : (value_pre < 100000000)) (PreH3 : (value_pre < 1000000000)) (PreH4 : (0 <= value_pre)) (PreH5 : (value_pre < INT_MAX)) ,
  TT && emp
|--
  “ (1 <= 8) ”
  &&  “ (8 < INT_MAX) ”
  &&  emp
.

Definition decimal_len_return_wit_9 :=
forall (value_pre: Z) (PreH1 : (value_pre >= 100000000)) (PreH2 : (value_pre < 1000000000)) (PreH3 : (0 <= value_pre)) (PreH4 : (value_pre < INT_MAX)) ,
  TT && emp
|--
  “ (1 <= 9) ”
  &&  “ (9 < INT_MAX) ”
  &&  emp
.

Definition decimal_len_return_wit_10 :=
forall (value_pre: Z) (PreH1 : (value_pre >= 1000000000)) (PreH2 : (0 <= value_pre)) (PreH3 : (value_pre < INT_MAX)) ,
  TT && emp
|--
  “ (1 <= 10) ”
  &&  “ (10 < INT_MAX) ”
  &&  emp
.

(*----- Function write_decimal -----*)

Definition write_decimal_safety_wit_1 :=
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (PreH1 : (0 <= value_pre)) (PreH2 : (value_pre < INT_MAX)) (PreH3 : (1 <= digits_pre)) (PreH4 : (digits_pre < INT_MAX)) ,
  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "tmp" ) )) # Int  |-> value_pre)
  **  ((( &( "digits" ) )) # Int  |-> digits_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "buf" ) )) # Ptr  |-> buf_pre)
  **  (CharArray.undef_full buf_pre (digits_pre + 1 ) )
|--
  “ ((digits_pre - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (digits_pre - 1 )) ”
.

Definition write_decimal_safety_wit_2 :=
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (PreH1 : (0 <= value_pre)) (PreH2 : (value_pre < INT_MAX)) (PreH3 : (1 <= digits_pre)) (PreH4 : (digits_pre < INT_MAX)) ,
  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "tmp" ) )) # Int  |-> value_pre)
  **  ((( &( "digits" ) )) # Int  |-> digits_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "buf" ) )) # Ptr  |-> buf_pre)
  **  (CharArray.undef_full buf_pre (digits_pre + 1 ) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition write_decimal_safety_wit_3 :=
forall (digits_pre: Z) (buf_pre: Z) (done: (@list Z)) (value: Z) (tmp: Z) (pos: Z) (PreH1 : ((-1) <= pos)) (PreH2 : (pos < digits_pre)) (PreH3 : (0 <= tmp)) (PreH4 : (tmp <= value)) (PreH5 : (1 <= digits_pre)) (PreH6 : (digits_pre < INT_MAX)) (PreH7 : (decimal_write_state_125 value tmp pos digits_pre done )) ,
  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "digits" ) )) # Int  |-> digits_pre)
  **  ((( &( "buf" ) )) # Ptr  |-> buf_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (CharArray.undef_seg buf_pre 0 (pos + 1 ) )
  **  (CharArray.full (buf_pre + ((pos + 1 ) * sizeof(CHAR) ) ) ((digits_pre - pos ) - 1 ) done )
  **  (CharArray.undef_seg buf_pre digits_pre (digits_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition write_decimal_safety_wit_4 :=
(
forall (digits_pre: Z) (buf_pre: Z) (done: (@list Z)) (value: Z) (tmp: Z) (pos: Z) (PreH1 : (pos >= 0)) (PreH2 : ((-1) <= pos)) (PreH3 : (pos < digits_pre)) (PreH4 : (0 <= tmp)) (PreH5 : (tmp <= value)) (PreH6 : (1 <= digits_pre)) (PreH7 : (digits_pre < INT_MAX)) (PreH8 : (decimal_write_state_125 value tmp pos digits_pre done )) ,
  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "digits" ) )) # Int  |-> digits_pre)
  **  ((( &( "buf" ) )) # Ptr  |-> buf_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (CharArray.undef_seg buf_pre 0 (pos + 1 ) )
  **  (CharArray.full (buf_pre + ((pos + 1 ) * sizeof(CHAR) ) ) ((digits_pre - pos ) - 1 ) done )
  **  (CharArray.undef_seg buf_pre digits_pre (digits_pre + 1 ) )
|--
  “ ((48 + (tmp % ( 10 ) ) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (48 + (tmp % ( 10 ) ) )) ”
) \/
(
forall (digits_pre: Z) (buf_pre: Z) (done: (@list Z)) (value: Z) (tmp: Z) (pos: Z) (PreH1 : (pos >= 0)) (PreH2 : ((-1) <= pos)) (PreH3 : (pos < digits_pre)) (PreH4 : (0 <= tmp)) (PreH5 : (tmp <= value)) (PreH6 : (1 <= digits_pre)) (PreH7 : (digits_pre < INT_MAX)) (PreH8 : (decimal_write_state_125 value tmp pos digits_pre done )) ,
  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "digits" ) )) # Int  |-> digits_pre)
  **  ((( &( "buf" ) )) # Ptr  |-> buf_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (CharArray.undef_seg buf_pre 0 (pos + 1 ) )
  **  (CharArray.full (buf_pre + ((pos + 1 ) * sizeof(CHAR) ) ) ((digits_pre - pos ) - 1 ) done )
  **  (CharArray.undef_seg buf_pre digits_pre (digits_pre + 1 ) )
|--
  “ ((48 + (tmp % ( 10 ) ) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (48 + (tmp % ( 10 ) ) )) ”
).

Definition write_decimal_safety_wit_4_split_goal_1 :=
forall (digits_pre: Z) (buf_pre: Z) (done: (@list Z)) (value: Z) (tmp: Z) (pos: Z) (PreH1 : (pos >= 0)) (PreH2 : ((-1) <= pos)) (PreH3 : (pos < digits_pre)) (PreH4 : (0 <= tmp)) (PreH5 : (tmp <= value)) (PreH6 : (1 <= digits_pre)) (PreH7 : (digits_pre < INT_MAX)) (PreH8 : (decimal_write_state_125 value tmp pos digits_pre done )) ,
  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "digits" ) )) # Int  |-> digits_pre)
  **  ((( &( "buf" ) )) # Ptr  |-> buf_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (CharArray.undef_seg buf_pre 0 (pos + 1 ) )
  **  (CharArray.full (buf_pre + ((pos + 1 ) * sizeof(CHAR) ) ) ((digits_pre - pos ) - 1 ) done )
  **  (CharArray.undef_seg buf_pre digits_pre (digits_pre + 1 ) )
|--
  “ ((48 + (tmp % ( 10 ) ) ) <= INT_MAX) ”
.

Definition write_decimal_safety_wit_4_split_goal_2 :=
forall (digits_pre: Z) (buf_pre: Z) (done: (@list Z)) (value: Z) (tmp: Z) (pos: Z) (PreH1 : (pos >= 0)) (PreH2 : ((-1) <= pos)) (PreH3 : (pos < digits_pre)) (PreH4 : (0 <= tmp)) (PreH5 : (tmp <= value)) (PreH6 : (1 <= digits_pre)) (PreH7 : (digits_pre < INT_MAX)) (PreH8 : (decimal_write_state_125 value tmp pos digits_pre done )) ,
  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "digits" ) )) # Int  |-> digits_pre)
  **  ((( &( "buf" ) )) # Ptr  |-> buf_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (CharArray.undef_seg buf_pre 0 (pos + 1 ) )
  **  (CharArray.full (buf_pre + ((pos + 1 ) * sizeof(CHAR) ) ) ((digits_pre - pos ) - 1 ) done )
  **  (CharArray.undef_seg buf_pre digits_pre (digits_pre + 1 ) )
|--
  “ ((INT_MIN) <= (48 + (tmp % ( 10 ) ) )) ”
.

Definition write_decimal_safety_wit_5 :=
forall (digits_pre: Z) (buf_pre: Z) (done: (@list Z)) (value: Z) (tmp: Z) (pos: Z) (PreH1 : (pos >= 0)) (PreH2 : ((-1) <= pos)) (PreH3 : (pos < digits_pre)) (PreH4 : (0 <= tmp)) (PreH5 : (tmp <= value)) (PreH6 : (1 <= digits_pre)) (PreH7 : (digits_pre < INT_MAX)) (PreH8 : (decimal_write_state_125 value tmp pos digits_pre done )) ,
  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "digits" ) )) # Int  |-> digits_pre)
  **  ((( &( "buf" ) )) # Ptr  |-> buf_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (CharArray.undef_seg buf_pre 0 (pos + 1 ) )
  **  (CharArray.full (buf_pre + ((pos + 1 ) * sizeof(CHAR) ) ) ((digits_pre - pos ) - 1 ) done )
  **  (CharArray.undef_seg buf_pre digits_pre (digits_pre + 1 ) )
|--
  “ ((tmp <> (INT_MIN)) \/ (10 <> (-1))) ”
  &&  “ (10 <> 0) ”
.

Definition write_decimal_safety_wit_6 :=
forall (digits_pre: Z) (buf_pre: Z) (done: (@list Z)) (value: Z) (tmp: Z) (pos: Z) (PreH1 : (pos >= 0)) (PreH2 : ((-1) <= pos)) (PreH3 : (pos < digits_pre)) (PreH4 : (0 <= tmp)) (PreH5 : (tmp <= value)) (PreH6 : (1 <= digits_pre)) (PreH7 : (digits_pre < INT_MAX)) (PreH8 : (decimal_write_state_125 value tmp pos digits_pre done )) ,
  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "digits" ) )) # Int  |-> digits_pre)
  **  ((( &( "buf" ) )) # Ptr  |-> buf_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (CharArray.undef_seg buf_pre 0 (pos + 1 ) )
  **  (CharArray.full (buf_pre + ((pos + 1 ) * sizeof(CHAR) ) ) ((digits_pre - pos ) - 1 ) done )
  **  (CharArray.undef_seg buf_pre digits_pre (digits_pre + 1 ) )
|--
  “ (48 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 48) ”
.

Definition write_decimal_safety_wit_7 :=
forall (digits_pre: Z) (buf_pre: Z) (done: (@list Z)) (value: Z) (tmp: Z) (pos: Z) (PreH1 : (pos >= 0)) (PreH2 : ((-1) <= pos)) (PreH3 : (pos < digits_pre)) (PreH4 : (0 <= tmp)) (PreH5 : (tmp <= value)) (PreH6 : (1 <= digits_pre)) (PreH7 : (digits_pre < INT_MAX)) (PreH8 : (decimal_write_state_125 value tmp pos digits_pre done )) ,
  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "digits" ) )) # Int  |-> digits_pre)
  **  ((( &( "buf" ) )) # Ptr  |-> buf_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (CharArray.undef_seg buf_pre 0 (pos + 1 ) )
  **  (CharArray.full (buf_pre + ((pos + 1 ) * sizeof(CHAR) ) ) ((digits_pre - pos ) - 1 ) done )
  **  (CharArray.undef_seg buf_pre digits_pre (digits_pre + 1 ) )
|--
  “ (10 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 10) ”
.

Definition write_decimal_safety_wit_8 :=
forall (digits_pre: Z) (buf_pre: Z) (done: (@list Z)) (value: Z) (tmp: Z) (pos: Z) (PreH1 : (0 <= ((digits_pre - pos ) - 1 ))) (PreH2 : (pos >= 0)) (PreH3 : ((-1) <= pos)) (PreH4 : (pos < digits_pre)) (PreH5 : (0 <= tmp)) (PreH6 : (tmp <= value)) (PreH7 : (1 <= digits_pre)) (PreH8 : (digits_pre < INT_MAX)) (PreH9 : (decimal_write_state_125 value tmp pos digits_pre done )) ,
  (((buf_pre + (pos * sizeof(CHAR) ) )) # Char  |-> (signed_last_nbits ((48 + (tmp % ( 10 ) ) )) (8)))
  **  (CharArray.undef_missing_i buf_pre pos 0 (pos + 1 ) )
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "digits" ) )) # Int  |-> digits_pre)
  **  ((( &( "buf" ) )) # Ptr  |-> buf_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (CharArray.full (buf_pre + ((pos + 1 ) * sizeof(CHAR) ) ) ((digits_pre - pos ) - 1 ) done )
  **  (CharArray.undef_seg buf_pre digits_pre (digits_pre + 1 ) )
|--
  “ ((tmp <> (INT_MIN)) \/ (10 <> (-1))) ”
  &&  “ (10 <> 0) ”
.

Definition write_decimal_safety_wit_9 :=
forall (digits_pre: Z) (buf_pre: Z) (done: (@list Z)) (value: Z) (tmp: Z) (pos: Z) (PreH1 : (0 <= ((digits_pre - pos ) - 1 ))) (PreH2 : (pos >= 0)) (PreH3 : ((-1) <= pos)) (PreH4 : (pos < digits_pre)) (PreH5 : (0 <= tmp)) (PreH6 : (tmp <= value)) (PreH7 : (1 <= digits_pre)) (PreH8 : (digits_pre < INT_MAX)) (PreH9 : (decimal_write_state_125 value tmp pos digits_pre done )) ,
  (((buf_pre + (pos * sizeof(CHAR) ) )) # Char  |-> (signed_last_nbits ((48 + (tmp % ( 10 ) ) )) (8)))
  **  (CharArray.undef_missing_i buf_pre pos 0 (pos + 1 ) )
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "digits" ) )) # Int  |-> digits_pre)
  **  ((( &( "buf" ) )) # Ptr  |-> buf_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (CharArray.full (buf_pre + ((pos + 1 ) * sizeof(CHAR) ) ) ((digits_pre - pos ) - 1 ) done )
  **  (CharArray.undef_seg buf_pre digits_pre (digits_pre + 1 ) )
|--
  “ (10 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 10) ”
.

Definition write_decimal_safety_wit_10 :=
forall (digits_pre: Z) (buf_pre: Z) (done: (@list Z)) (value: Z) (tmp: Z) (pos: Z) (PreH1 : (0 <= ((digits_pre - pos ) - 1 ))) (PreH2 : (pos >= 0)) (PreH3 : ((-1) <= pos)) (PreH4 : (pos < digits_pre)) (PreH5 : (0 <= tmp)) (PreH6 : (tmp <= value)) (PreH7 : (1 <= digits_pre)) (PreH8 : (digits_pre < INT_MAX)) (PreH9 : (decimal_write_state_125 value tmp pos digits_pre done )) ,
  (((buf_pre + (pos * sizeof(CHAR) ) )) # Char  |-> (signed_last_nbits ((48 + (tmp % ( 10 ) ) )) (8)))
  **  (CharArray.undef_missing_i buf_pre pos 0 (pos + 1 ) )
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "digits" ) )) # Int  |-> digits_pre)
  **  ((( &( "buf" ) )) # Ptr  |-> buf_pre)
  **  ((( &( "tmp" ) )) # Int  |-> (tmp ÷ 10 ))
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (CharArray.full (buf_pre + ((pos + 1 ) * sizeof(CHAR) ) ) ((digits_pre - pos ) - 1 ) done )
  **  (CharArray.undef_seg buf_pre digits_pre (digits_pre + 1 ) )
|--
  “ ((pos - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (pos - 1 )) ”
.

Definition write_decimal_safety_wit_11 :=
forall (digits_pre: Z) (buf_pre: Z) (done: (@list Z)) (value: Z) (tmp: Z) (pos: Z) (PreH1 : (pos < 0)) (PreH2 : ((-1) <= pos)) (PreH3 : (pos < digits_pre)) (PreH4 : (0 <= tmp)) (PreH5 : (tmp <= value)) (PreH6 : (1 <= digits_pre)) (PreH7 : (digits_pre < INT_MAX)) (PreH8 : (decimal_write_state_125 value tmp pos digits_pre done )) ,
  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "digits" ) )) # Int  |-> digits_pre)
  **  ((( &( "buf" ) )) # Ptr  |-> buf_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (CharArray.undef_seg buf_pre 0 (pos + 1 ) )
  **  (CharArray.full (buf_pre + ((pos + 1 ) * sizeof(CHAR) ) ) ((digits_pre - pos ) - 1 ) done )
  **  (CharArray.undef_seg buf_pre digits_pre (digits_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition write_decimal_entail_wit_1 :=
(
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (PreH1 : (0 <= value_pre)) (PreH2 : (value_pre < INT_MAX)) (PreH3 : (1 <= digits_pre)) (PreH4 : (digits_pre < INT_MAX)) ,
  (CharArray.undef_full buf_pre (digits_pre + 1 ) )
|--
  EX (done: (@list Z)) ,
  “ ((-1) <= (digits_pre - 1 )) ”
  &&  “ ((digits_pre - 1 ) < digits_pre) ”
  &&  “ (0 <= value_pre) ”
  &&  “ (value_pre <= value_pre) ”
  &&  “ (1 <= digits_pre) ”
  &&  “ (digits_pre < INT_MAX) ”
  &&  “ (decimal_write_state_125 value_pre value_pre (digits_pre - 1 ) digits_pre done ) ”
  &&  (CharArray.undef_seg buf_pre 0 ((digits_pre - 1 ) + 1 ) )
  **  (CharArray.full (buf_pre + (((digits_pre - 1 ) + 1 ) * sizeof(CHAR) ) ) ((digits_pre - (digits_pre - 1 ) ) - 1 ) done )
  **  (CharArray.undef_seg buf_pre digits_pre (digits_pre + 1 ) )
) \/
(
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (PreH1 : (0 <= value_pre)) (PreH2 : (value_pre < INT_MAX)) (PreH3 : (1 <= digits_pre)) (PreH4 : (digits_pre < INT_MAX)) ,
  (CharArray.undef_full buf_pre (digits_pre + 1 ) )
|--
  “ (decimal_write_state_125 value_pre value_pre (digits_pre - 1 ) digits_pre (@nil Z) ) ”
  &&  (CharArray.undef_full buf_pre ((digits_pre - 1 ) + 1 ) )
  **  (CharArray.undef_seg buf_pre digits_pre (digits_pre + 1 ) )
).

Definition write_decimal_entail_wit_1_split_goal_1 :=
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (PreH1 : (0 <= value_pre)) (PreH2 : (value_pre < INT_MAX)) (PreH3 : (1 <= digits_pre)) (PreH4 : (digits_pre < INT_MAX)) ,
  (CharArray.undef_full buf_pre (digits_pre + 1 ) )
|--
  “ (decimal_write_state_125 value_pre value_pre (digits_pre - 1 ) digits_pre (@nil Z) ) ”
.

Definition write_decimal_entail_wit_1_split_goal_spatial :=
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (PreH1 : (0 <= value_pre)) (PreH2 : (value_pre < INT_MAX)) (PreH3 : (1 <= digits_pre)) (PreH4 : (digits_pre < INT_MAX)) ,
  (CharArray.undef_full buf_pre (digits_pre + 1 ) )
|--
  (CharArray.undef_full buf_pre ((digits_pre - 1 ) + 1 ) )
  **  (CharArray.undef_seg buf_pre digits_pre (digits_pre + 1 ) )
.

Definition write_decimal_entail_wit_2 :=
(
forall (digits_pre: Z) (buf_pre: Z) (done_2: (@list Z)) (value: Z) (tmp: Z) (pos: Z) (PreH1 : (0 <= ((digits_pre - pos ) - 1 ))) (PreH2 : (pos >= 0)) (PreH3 : ((-1) <= pos)) (PreH4 : (pos < digits_pre)) (PreH5 : (0 <= tmp)) (PreH6 : (tmp <= value)) (PreH7 : (1 <= digits_pre)) (PreH8 : (digits_pre < INT_MAX)) (PreH9 : (decimal_write_state_125 value tmp pos digits_pre done_2 )) ,
  (((buf_pre + (pos * sizeof(CHAR) ) )) # Char  |-> (signed_last_nbits ((48 + (tmp % ( 10 ) ) )) (8)))
  **  (CharArray.undef_missing_i buf_pre pos 0 (pos + 1 ) )
  **  (CharArray.full (buf_pre + ((pos + 1 ) * sizeof(CHAR) ) ) ((digits_pre - pos ) - 1 ) done_2 )
  **  (CharArray.undef_seg buf_pre digits_pre (digits_pre + 1 ) )
|--
  EX (done: (@list Z)) ,
  “ ((-1) <= (pos - 1 )) ”
  &&  “ ((pos - 1 ) < digits_pre) ”
  &&  “ (0 <= (tmp ÷ 10 )) ”
  &&  “ ((tmp ÷ 10 ) <= value) ”
  &&  “ (1 <= digits_pre) ”
  &&  “ (digits_pre < INT_MAX) ”
  &&  “ (decimal_write_state_125 value (tmp ÷ 10 ) (pos - 1 ) digits_pre done ) ”
  &&  (CharArray.undef_seg buf_pre 0 ((pos - 1 ) + 1 ) )
  **  (CharArray.full (buf_pre + (((pos - 1 ) + 1 ) * sizeof(CHAR) ) ) ((digits_pre - (pos - 1 ) ) - 1 ) done )
  **  (CharArray.undef_seg buf_pre digits_pre (digits_pre + 1 ) )
) \/
(
forall (digits_pre: Z) (buf_pre: Z) (done_2: (@list Z)) (value: Z) (tmp: Z) (pos: Z) (PreH1 : (0 <= ((digits_pre - pos ) - 1 ))) (PreH2 : (pos >= 0)) (PreH3 : ((-1) <= pos)) (PreH4 : (pos < digits_pre)) (PreH5 : (0 <= tmp)) (PreH6 : (tmp <= value)) (PreH7 : (1 <= digits_pre)) (PreH8 : (digits_pre < INT_MAX)) (PreH9 : (decimal_write_state_125 value tmp pos digits_pre done_2 )) ,
  (((buf_pre + (pos * sizeof(CHAR) ) )) # Char  |-> (signed_last_nbits ((48 + (tmp % ( 10 ) ) )) (8)))
  **  (CharArray.undef_missing_i buf_pre pos 0 (pos + 1 ) )
  **  (CharArray.full (buf_pre + ((pos + 1 ) * sizeof(CHAR) ) ) ((digits_pre - pos ) - 1 ) done_2 )
|--
  EX (done: (@list Z)) ,
  “ ((-1) <= (pos - 1 )) ”
  &&  “ ((pos - 1 ) < digits_pre) ”
  &&  “ (0 <= (tmp ÷ 10 )) ”
  &&  “ ((tmp ÷ 10 ) <= value) ”
  &&  “ (1 <= digits_pre) ”
  &&  “ (digits_pre < INT_MAX) ”
  &&  “ (decimal_write_state_125 value (tmp ÷ 10 ) (pos - 1 ) digits_pre done ) ”
  &&  (CharArray.undef_full buf_pre ((pos - 1 ) + 1 ) )
  **  (CharArray.full (buf_pre + (((pos - 1 ) + 1 ) * sizeof(CHAR) ) ) ((digits_pre - (pos - 1 ) ) - 1 ) done )
).

Definition write_decimal_return_wit_1 :=
(
forall (digits_pre: Z) (buf_pre: Z) (done: (@list Z)) (value: Z) (tmp: Z) (pos: Z) (PreH1 : (0 <= ((digits_pre - pos ) - 1 ))) (PreH2 : (pos < 0)) (PreH3 : ((-1) <= pos)) (PreH4 : (pos < digits_pre)) (PreH5 : (0 <= tmp)) (PreH6 : (tmp <= value)) (PreH7 : (1 <= digits_pre)) (PreH8 : (digits_pre < INT_MAX)) (PreH9 : (decimal_write_state_125 value tmp pos digits_pre done )) ,
  (CharArray.undef_seg buf_pre (digits_pre + 1 ) (digits_pre + 1 ) )
  **  (((buf_pre + (digits_pre * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (CharArray.full (buf_pre + ((pos + 1 ) * sizeof(CHAR) ) ) ((digits_pre - pos ) - 1 ) done )
|--
  EX (out_l: (@list Z)) ,
  “ ((Zlength (out_l)) = digits_pre) ”
  &&  (CharArray.full buf_pre (digits_pre + 1 ) (c_string (out_l)) )
) \/
(
forall (digits_pre: Z) (buf_pre: Z) (done: (@list Z)) (value: Z) (tmp: Z) (pos: Z) (PreH1 : (0 <= ((digits_pre - pos ) - 1 ))) (PreH2 : (pos < 0)) (PreH3 : ((-1) <= pos)) (PreH4 : (pos < digits_pre)) (PreH5 : (0 <= tmp)) (PreH6 : (tmp <= value)) (PreH7 : (1 <= digits_pre)) (PreH8 : (digits_pre < INT_MAX)) (PreH9 : (decimal_write_state_125 value tmp pos digits_pre done )) ,
  (((buf_pre + (digits_pre * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (CharArray.full (buf_pre + ((pos + 1 ) * sizeof(CHAR) ) ) ((digits_pre - pos ) - 1 ) done )
|--
  EX (out_l: (@list Z)) ,
  “ ((Zlength (out_l)) = digits_pre) ”
  &&  (CharArray.full buf_pre (digits_pre + 1 ) (c_string (out_l)) )
).

Definition write_decimal_partial_solve_wit_1 :=
forall (digits_pre: Z) (buf_pre: Z) (done: (@list Z)) (value: Z) (tmp: Z) (pos: Z) (PreH1 : (pos >= 0)) (PreH2 : ((-1) <= pos)) (PreH3 : (pos < digits_pre)) (PreH4 : (0 <= tmp)) (PreH5 : (tmp <= value)) (PreH6 : (1 <= digits_pre)) (PreH7 : (digits_pre < INT_MAX)) (PreH8 : (decimal_write_state_125 value tmp pos digits_pre done )) ,
  (CharArray.undef_seg buf_pre 0 (pos + 1 ) )
  **  (CharArray.full (buf_pre + ((pos + 1 ) * sizeof(CHAR) ) ) ((digits_pre - pos ) - 1 ) done )
  **  (CharArray.undef_seg buf_pre digits_pre (digits_pre + 1 ) )
|--
  “ (0 <= ((digits_pre - pos ) - 1 )) ”
  &&  “ (pos >= 0) ”
  &&  “ ((-1) <= pos) ”
  &&  “ (pos < digits_pre) ”
  &&  “ (0 <= tmp) ”
  &&  “ (tmp <= value) ”
  &&  “ (1 <= digits_pre) ”
  &&  “ (digits_pre < INT_MAX) ”
  &&  “ (decimal_write_state_125 value tmp pos digits_pre done ) ”
  &&  (((buf_pre + (pos * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i buf_pre pos 0 (pos + 1 ) )
  **  (CharArray.full (buf_pre + ((pos + 1 ) * sizeof(CHAR) ) ) ((digits_pre - pos ) - 1 ) done )
  **  (CharArray.undef_seg buf_pre digits_pre (digits_pre + 1 ) )
.

Definition write_decimal_partial_solve_wit_2 :=
forall (digits_pre: Z) (buf_pre: Z) (done: (@list Z)) (value: Z) (tmp: Z) (pos: Z) (PreH1 : (pos < 0)) (PreH2 : ((-1) <= pos)) (PreH3 : (pos < digits_pre)) (PreH4 : (0 <= tmp)) (PreH5 : (tmp <= value)) (PreH6 : (1 <= digits_pre)) (PreH7 : (digits_pre < INT_MAX)) (PreH8 : (decimal_write_state_125 value tmp pos digits_pre done )) ,
  (CharArray.undef_seg buf_pre 0 (pos + 1 ) )
  **  (CharArray.full (buf_pre + ((pos + 1 ) * sizeof(CHAR) ) ) ((digits_pre - pos ) - 1 ) done )
  **  (CharArray.undef_seg buf_pre digits_pre (digits_pre + 1 ) )
|--
  “ (0 <= ((digits_pre - pos ) - 1 )) ”
  &&  “ (pos < 0) ”
  &&  “ ((-1) <= pos) ”
  &&  “ (pos < digits_pre) ”
  &&  “ (0 <= tmp) ”
  &&  “ (tmp <= value) ”
  &&  “ (1 <= digits_pre) ”
  &&  “ (digits_pre < INT_MAX) ”
  &&  “ (decimal_write_state_125 value tmp pos digits_pre done ) ”
  &&  (((buf_pre + (digits_pre * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i buf_pre digits_pre digits_pre (digits_pre + 1 ) )
  **  (CharArray.full (buf_pre + ((pos + 1 ) * sizeof(CHAR) ) ) ((digits_pre - pos ) - 1 ) done )
.

(*----- Function split_words -----*)

Definition split_words_safety_wit_1 :=
forall (txt_pre: Z) (str_l: (@list Z)) (PreH1 : (valid_string str_l )) (PreH2 : (all_ascii str_l )) (PreH3 : (valid_split_words_input_125 str_l )) (PreH4 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH5 : (problem_125_pre_z str_l )) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  (store_string txt_pre str_l )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_words_safety_wit_2 :=
forall (txt_pre: Z) (str_l: (@list Z)) (PreH1 : (valid_string str_l )) (PreH2 : (all_ascii str_l )) (PreH3 : (valid_split_words_input_125 str_l )) (PreH4 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH5 : (problem_125_pre_z str_l )) ,
  ((( &( "data" ) )) # Ptr  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> 0)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  (store_string txt_pre str_l )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_words_safety_wit_3 :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (valid_string str_l )) (PreH4 : (all_ascii str_l )) (PreH5 : (valid_split_words_input_125 str_l )) (PreH6 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH7 : (problem_125_pre_z str_l )) ,
  ((( &( "space_hit" ) )) # Ptr  |->_)
  **  (store_string txt_pre str_l )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "data" ) )) # Ptr  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> 0)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (32 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 32) ”
.

Definition split_words_safety_wit_4 :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH2 : (retval = (string_length (str_l)))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (valid_string str_l )) (PreH5 : (all_ascii str_l )) (PreH6 : (valid_split_words_input_125 str_l )) (PreH7 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH8 : (problem_125_pre_z str_l )) ,
  ((( &( "comma_hit" ) )) # Ptr  |->_)
  **  (store_string txt_pre str_l )
  **  ((( &( "space_hit" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "data" ) )) # Ptr  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> 0)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (44 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 44) ”
.

Definition split_words_safety_wit_5 :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (strchr_result str_l 44 retval_3 txt_pre )) (PreH3 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH4 : (retval = (string_length (str_l)))) (PreH5 : (0 <= ((string_length (str_l)) + 1 ))) (PreH6 : (valid_string str_l )) (PreH7 : (all_ascii str_l )) (PreH8 : (valid_split_words_input_125 str_l )) (PreH9 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH10 : (problem_125_pre_z str_l )) ,
  ((&((retval_4)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "comma_hit" ) )) # Ptr  |-> retval_3)
  **  ((( &( "space_hit" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "data" ) )) # Ptr  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval_4)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_words_safety_wit_6 :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (strchr_result str_l 44 retval_3 txt_pre )) (PreH3 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH4 : (retval = (string_length (str_l)))) (PreH5 : (0 <= ((string_length (str_l)) + 1 ))) (PreH6 : (valid_string str_l )) (PreH7 : (all_ascii str_l )) (PreH8 : (valid_split_words_input_125 str_l )) (PreH9 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH10 : (problem_125_pre_z str_l )) ,
  ((&((retval_4)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "comma_hit" ) )) # Ptr  |-> retval_3)
  **  ((( &( "space_hit" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "data" ) )) # Ptr  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval_4)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition split_words_safety_wit_7 :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (strchr_result str_l 44 retval_3 txt_pre )) (PreH3 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH4 : (retval = (string_length (str_l)))) (PreH5 : (0 <= ((string_length (str_l)) + 1 ))) (PreH6 : (valid_string str_l )) (PreH7 : (all_ascii str_l )) (PreH8 : (valid_split_words_input_125 str_l )) (PreH9 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH10 : (problem_125_pre_z str_l )) ,
  ((&((retval_4)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "comma_hit" ) )) # Ptr  |-> retval_3)
  **  ((( &( "space_hit" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "data" ) )) # Ptr  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval_4)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition split_words_safety_wit_8 :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 <> 0)) (PreH2 : (retval_4 <> 0)) (PreH3 : (strchr_result str_l 44 retval_3 txt_pre )) (PreH4 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH5 : (retval = (string_length (str_l)))) (PreH6 : (0 <= ((string_length (str_l)) + 1 ))) (PreH7 : (valid_string str_l )) (PreH8 : (all_ascii str_l )) (PreH9 : (valid_split_words_input_125 str_l )) (PreH10 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH11 : (problem_125_pre_z str_l )) ,
  (PtrArray.undef_full retval_5 (retval + 1 ) )
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_5)
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "comma_hit" ) )) # Ptr  |-> retval_3)
  **  ((( &( "space_hit" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "data" ) )) # Ptr  |-> retval_5)
  **  ((( &( "out" ) )) # Ptr  |-> retval_4)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_words_safety_wit_9 :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_5 <> 0)) (PreH3 : (retval_4 <> 0)) (PreH4 : (strchr_result str_l 44 retval_3 txt_pre )) (PreH5 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH6 : (retval = (string_length (str_l)))) (PreH7 : (0 <= ((string_length (str_l)) + 1 ))) (PreH8 : (valid_string str_l )) (PreH9 : (all_ascii str_l )) (PreH10 : (valid_split_words_input_125 str_l )) (PreH11 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH12 : (problem_125_pre_z str_l )) ,
  (PtrArray.undef_full retval_5 (retval + 1 ) )
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_5)
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "comma_hit" ) )) # Ptr  |-> retval_3)
  **  ((( &( "space_hit" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "data" ) )) # Ptr  |-> retval_5)
  **  ((( &( "out" ) )) # Ptr  |-> retval_4)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_words_safety_wit_10 :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_5 <> 0)) (PreH3 : (retval_4 <> 0)) (PreH4 : (strchr_result str_l 44 retval_3 txt_pre )) (PreH5 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH6 : (retval = (string_length (str_l)))) (PreH7 : (0 <= ((string_length (str_l)) + 1 ))) (PreH8 : (valid_string str_l )) (PreH9 : (all_ascii str_l )) (PreH10 : (valid_split_words_input_125 str_l )) (PreH11 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH12 : (problem_125_pre_z str_l )) ,
  ((( &( "sep" ) )) # Int  |->_)
  **  (PtrArray.undef_full retval_5 (retval + 1 ) )
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_5)
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "comma_hit" ) )) # Ptr  |-> retval_3)
  **  ((( &( "space_hit" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "data" ) )) # Ptr  |-> retval_5)
  **  ((( &( "out" ) )) # Ptr  |-> retval_4)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_words_safety_wit_11 :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_5 <> 0)) (PreH4 : (retval_4 <> 0)) (PreH5 : (strchr_result str_l 44 retval_3 txt_pre )) (PreH6 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH7 : (retval = (string_length (str_l)))) (PreH8 : (0 <= ((string_length (str_l)) + 1 ))) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (valid_split_words_input_125 str_l )) (PreH12 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH13 : (problem_125_pre_z str_l )) ,
  ((( &( "sep" ) )) # Int  |->_)
  **  (PtrArray.undef_full retval_5 (retval + 1 ) )
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_5)
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "comma_hit" ) )) # Ptr  |-> retval_3)
  **  ((( &( "space_hit" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "data" ) )) # Ptr  |-> retval_5)
  **  ((( &( "out" ) )) # Ptr  |-> retval_4)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ False ”
.

Definition split_words_safety_wit_12 :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_5 <> 0)) (PreH4 : (retval_4 <> 0)) (PreH5 : (strchr_result str_l 44 retval_3 txt_pre )) (PreH6 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH7 : (retval = (string_length (str_l)))) (PreH8 : (0 <= ((string_length (str_l)) + 1 ))) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (valid_split_words_input_125 str_l )) (PreH12 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH13 : (problem_125_pre_z str_l )) ,
  ((( &( "sep" ) )) # Int  |->_)
  **  (PtrArray.undef_full retval_5 (retval + 1 ) )
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_5)
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "comma_hit" ) )) # Ptr  |-> retval_3)
  **  ((( &( "space_hit" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "data" ) )) # Ptr  |-> retval_5)
  **  ((( &( "out" ) )) # Ptr  |-> retval_4)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (32 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 32) ”
.

Definition split_words_safety_wit_13 :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 = 0)) (PreH3 : (retval_5 <> 0)) (PreH4 : (retval_4 <> 0)) (PreH5 : (strchr_result str_l 44 retval_3 txt_pre )) (PreH6 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH7 : (retval = (string_length (str_l)))) (PreH8 : (0 <= ((string_length (str_l)) + 1 ))) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (valid_split_words_input_125 str_l )) (PreH12 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH13 : (problem_125_pre_z str_l )) ,
  ((( &( "sep" ) )) # Int  |->_)
  **  (PtrArray.undef_full retval_5 (retval + 1 ) )
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_5)
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "comma_hit" ) )) # Ptr  |-> retval_3)
  **  ((( &( "space_hit" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "data" ) )) # Ptr  |-> retval_5)
  **  ((( &( "out" ) )) # Ptr  |-> retval_4)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_words_safety_wit_14 :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_2 = 0)) (PreH4 : (retval_5 <> 0)) (PreH5 : (retval_4 <> 0)) (PreH6 : (strchr_result str_l 44 retval_3 txt_pre )) (PreH7 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH8 : (retval = (string_length (str_l)))) (PreH9 : (0 <= ((string_length (str_l)) + 1 ))) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (valid_split_words_input_125 str_l )) (PreH13 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH14 : (problem_125_pre_z str_l )) ,
  ((( &( "sep" ) )) # Int  |->_)
  **  (PtrArray.undef_full retval_5 (retval + 1 ) )
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_5)
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "comma_hit" ) )) # Ptr  |-> retval_3)
  **  ((( &( "space_hit" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "data" ) )) # Ptr  |-> retval_5)
  **  ((( &( "out" ) )) # Ptr  |-> retval_4)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ False ”
.

Definition split_words_safety_wit_15 :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_2 = 0)) (PreH4 : (retval_5 <> 0)) (PreH5 : (retval_4 <> 0)) (PreH6 : (strchr_result str_l 44 retval_3 txt_pre )) (PreH7 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH8 : (retval = (string_length (str_l)))) (PreH9 : (0 <= ((string_length (str_l)) + 1 ))) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (valid_split_words_input_125 str_l )) (PreH13 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH14 : (problem_125_pre_z str_l )) ,
  ((( &( "sep" ) )) # Int  |->_)
  **  (PtrArray.undef_full retval_5 (retval + 1 ) )
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_5)
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "comma_hit" ) )) # Ptr  |-> retval_3)
  **  ((( &( "space_hit" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "data" ) )) # Ptr  |-> retval_5)
  **  ((( &( "out" ) )) # Ptr  |-> retval_4)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (44 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 44) ”
.

Definition split_words_safety_wit_16 :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_5 <> 0)) (PreH4 : (retval_4 <> 0)) (PreH5 : (strchr_result str_l 44 retval_3 txt_pre )) (PreH6 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH7 : (retval = (string_length (str_l)))) (PreH8 : (0 <= ((string_length (str_l)) + 1 ))) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (valid_split_words_input_125 str_l )) (PreH12 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH13 : (problem_125_pre_z str_l )) ,
  ((( &( "start" ) )) # Int  |->_)
  **  ((( &( "sep" ) )) # Int  |-> 32)
  **  (PtrArray.undef_full retval_5 (retval + 1 ) )
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_5)
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "comma_hit" ) )) # Ptr  |-> retval_3)
  **  ((( &( "space_hit" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "data" ) )) # Ptr  |-> retval_5)
  **  ((( &( "out" ) )) # Ptr  |-> retval_4)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition split_words_safety_wit_17 :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_5 <> 0)) (PreH4 : (retval_4 <> 0)) (PreH5 : (strchr_result str_l 44 retval_3 txt_pre )) (PreH6 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH7 : (retval = (string_length (str_l)))) (PreH8 : (0 <= ((string_length (str_l)) + 1 ))) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (valid_split_words_input_125 str_l )) (PreH12 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH13 : (problem_125_pre_z str_l )) ,
  ((( &( "start" ) )) # Int  |->_)
  **  ((( &( "sep" ) )) # Int  |-> 32)
  **  (PtrArray.undef_full retval_5 (retval + 1 ) )
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_5)
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "comma_hit" ) )) # Ptr  |-> retval_3)
  **  ((( &( "space_hit" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "data" ) )) # Ptr  |-> retval_5)
  **  ((( &( "out" ) )) # Ptr  |-> retval_4)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition split_words_safety_wit_18 :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_2 = 0)) (PreH4 : (retval_5 <> 0)) (PreH5 : (retval_4 <> 0)) (PreH6 : (strchr_result str_l 44 retval_3 txt_pre )) (PreH7 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH8 : (retval = (string_length (str_l)))) (PreH9 : (0 <= ((string_length (str_l)) + 1 ))) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (valid_split_words_input_125 str_l )) (PreH13 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH14 : (problem_125_pre_z str_l )) ,
  ((( &( "start" ) )) # Int  |->_)
  **  ((( &( "sep" ) )) # Int  |-> 44)
  **  (PtrArray.undef_full retval_5 (retval + 1 ) )
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_5)
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "comma_hit" ) )) # Ptr  |-> retval_3)
  **  ((( &( "space_hit" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "data" ) )) # Ptr  |-> retval_5)
  **  ((( &( "out" ) )) # Ptr  |-> retval_4)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition split_words_safety_wit_19 :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_2 = 0)) (PreH4 : (retval_5 <> 0)) (PreH5 : (retval_4 <> 0)) (PreH6 : (strchr_result str_l 44 retval_3 txt_pre )) (PreH7 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH8 : (retval = (string_length (str_l)))) (PreH9 : (0 <= ((string_length (str_l)) + 1 ))) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (valid_split_words_input_125 str_l )) (PreH13 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH14 : (problem_125_pre_z str_l )) ,
  ((( &( "start" ) )) # Int  |->_)
  **  ((( &( "sep" ) )) # Int  |-> 44)
  **  (PtrArray.undef_full retval_5 (retval + 1 ) )
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_5)
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "comma_hit" ) )) # Ptr  |-> retval_3)
  **  ((( &( "space_hit" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "data" ) )) # Ptr  |-> retval_5)
  **  ((( &( "out" ) )) # Ptr  |-> retval_4)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition split_words_safety_wit_20 :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_5 <> 0)) (PreH4 : (retval_4 <> 0)) (PreH5 : (strchr_result str_l 44 retval_3 txt_pre )) (PreH6 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH7 : (retval = (string_length (str_l)))) (PreH8 : (0 <= ((string_length (str_l)) + 1 ))) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (valid_split_words_input_125 str_l )) (PreH12 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH13 : (problem_125_pre_z str_l )) ,
  ((( &( "out_size" ) )) # Int  |->_)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "sep" ) )) # Int  |-> 32)
  **  (PtrArray.undef_full retval_5 (retval + 1 ) )
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_5)
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "comma_hit" ) )) # Ptr  |-> retval_3)
  **  ((( &( "space_hit" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "data" ) )) # Ptr  |-> retval_5)
  **  ((( &( "out" ) )) # Ptr  |-> retval_4)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_words_safety_wit_21 :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_2 = 0)) (PreH4 : (retval_5 <> 0)) (PreH5 : (retval_4 <> 0)) (PreH6 : (strchr_result str_l 44 retval_3 txt_pre )) (PreH7 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH8 : (retval = (string_length (str_l)))) (PreH9 : (0 <= ((string_length (str_l)) + 1 ))) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (valid_split_words_input_125 str_l )) (PreH13 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH14 : (problem_125_pre_z str_l )) ,
  ((( &( "out_size" ) )) # Int  |->_)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "sep" ) )) # Int  |-> 44)
  **  (PtrArray.undef_full retval_5 (retval + 1 ) )
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_5)
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "comma_hit" ) )) # Ptr  |-> retval_3)
  **  ((( &( "space_hit" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "data" ) )) # Ptr  |-> retval_5)
  **  ((( &( "out" ) )) # Ptr  |-> retval_4)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_words_safety_wit_22 :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_5 <> 0)) (PreH4 : (retval_4 <> 0)) (PreH5 : (strchr_result str_l 44 retval_3 txt_pre )) (PreH6 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH7 : (retval = (string_length (str_l)))) (PreH8 : (0 <= ((string_length (str_l)) + 1 ))) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (valid_split_words_input_125 str_l )) (PreH12 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH13 : (problem_125_pre_z str_l )) ,
  ((( &( "ch" ) )) # Int  |->_)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "sep" ) )) # Int  |-> 32)
  **  (PtrArray.undef_full retval_5 (retval + 1 ) )
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_5)
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "comma_hit" ) )) # Ptr  |-> retval_3)
  **  ((( &( "space_hit" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "data" ) )) # Ptr  |-> retval_5)
  **  ((( &( "out" ) )) # Ptr  |-> retval_4)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_words_safety_wit_23 :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_2 = 0)) (PreH4 : (retval_5 <> 0)) (PreH5 : (retval_4 <> 0)) (PreH6 : (strchr_result str_l 44 retval_3 txt_pre )) (PreH7 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH8 : (retval = (string_length (str_l)))) (PreH9 : (0 <= ((string_length (str_l)) + 1 ))) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (valid_split_words_input_125 str_l )) (PreH13 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH14 : (problem_125_pre_z str_l )) ,
  ((( &( "ch" ) )) # Int  |->_)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "sep" ) )) # Int  |-> 44)
  **  (PtrArray.undef_full retval_5 (retval + 1 ) )
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_5)
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "comma_hit" ) )) # Ptr  |-> retval_3)
  **  ((( &( "space_hit" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "data" ) )) # Ptr  |-> retval_5)
  **  ((( &( "out" ) )) # Ptr  |-> retval_4)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_words_safety_wit_24 :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_5 <> 0)) (PreH4 : (retval_4 <> 0)) (PreH5 : (strchr_result str_l 44 retval_3 txt_pre )) (PreH6 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH7 : (retval = (string_length (str_l)))) (PreH8 : (0 <= ((string_length (str_l)) + 1 ))) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (valid_split_words_input_125 str_l )) (PreH12 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH13 : (problem_125_pre_z str_l )) ,
  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "sep" ) )) # Int  |-> 32)
  **  (PtrArray.undef_full retval_5 (retval + 1 ) )
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_5)
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "comma_hit" ) )) # Ptr  |-> retval_3)
  **  ((( &( "space_hit" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "data" ) )) # Ptr  |-> retval_5)
  **  ((( &( "out" ) )) # Ptr  |-> retval_4)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_words_safety_wit_25 :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_2 = 0)) (PreH4 : (retval_5 <> 0)) (PreH5 : (retval_4 <> 0)) (PreH6 : (strchr_result str_l 44 retval_3 txt_pre )) (PreH7 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH8 : (retval = (string_length (str_l)))) (PreH9 : (0 <= ((string_length (str_l)) + 1 ))) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (valid_split_words_input_125 str_l )) (PreH13 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH14 : (problem_125_pre_z str_l )) ,
  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "sep" ) )) # Int  |-> 44)
  **  (PtrArray.undef_full retval_5 (retval + 1 ) )
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_5)
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "comma_hit" ) )) # Ptr  |-> retval_3)
  **  ((( &( "space_hit" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "data" ) )) # Ptr  |-> retval_5)
  **  ((( &( "out" ) )) # Ptr  |-> retval_4)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_words_safety_wit_26 :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_5 <> 0)) (PreH4 : (retval_4 <> 0)) (PreH5 : (strchr_result str_l 44 retval_3 txt_pre )) (PreH6 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH7 : (retval = (string_length (str_l)))) (PreH8 : (0 <= ((string_length (str_l)) + 1 ))) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (valid_split_words_input_125 str_l )) (PreH12 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH13 : (problem_125_pre_z str_l )) ,
  ((( &( "w" ) )) # Ptr  |->_)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "sep" ) )) # Int  |-> 32)
  **  (PtrArray.undef_full retval_5 (retval + 1 ) )
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_5)
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "comma_hit" ) )) # Ptr  |-> retval_3)
  **  ((( &( "space_hit" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "data" ) )) # Ptr  |-> retval_5)
  **  ((( &( "out" ) )) # Ptr  |-> retval_4)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_words_safety_wit_27 :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_2 = 0)) (PreH4 : (retval_5 <> 0)) (PreH5 : (retval_4 <> 0)) (PreH6 : (strchr_result str_l 44 retval_3 txt_pre )) (PreH7 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH8 : (retval = (string_length (str_l)))) (PreH9 : (0 <= ((string_length (str_l)) + 1 ))) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (valid_split_words_input_125 str_l )) (PreH13 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH14 : (problem_125_pre_z str_l )) ,
  ((( &( "w" ) )) # Ptr  |->_)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "sep" ) )) # Int  |-> 44)
  **  (PtrArray.undef_full retval_5 (retval + 1 ) )
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_5)
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "comma_hit" ) )) # Ptr  |-> retval_3)
  **  ((( &( "space_hit" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "data" ) )) # Ptr  |-> retval_5)
  **  ((( &( "out" ) )) # Ptr  |-> retval_4)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_words_safety_wit_28 :=
forall (txt_pre: Z) (str_l: (@list Z)) (n: Z) (out: Z) (data: Z) (w: Z) (out_size: Z) (start: Z) (ch: Z) (len: Z) (comma_hit: Z) (space_hit: Z) (sep: Z) (PreH1 : (n = (string_length (str_l)))) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (w = 0)) (PreH5 : (out_size = 0)) (PreH6 : (start = (-1))) (PreH7 : (ch = 0)) (PreH8 : (len = 0)) (PreH9 : (space_hit <> 0)) (PreH10 : ((contains_zb_125 (str_l) (32)) = true)) (PreH11 : (sep = 32)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (valid_split_words_input_125 str_l )) (PreH15 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH16 : (problem_125_pre_z str_l )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string txt_pre str_l )
  **  (PtrArray.undef_full data (n + 1 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_words_safety_wit_29 :=
forall (txt_pre: Z) (str_l: (@list Z)) (n: Z) (out: Z) (data: Z) (w: Z) (out_size: Z) (start: Z) (ch: Z) (len: Z) (comma_hit: Z) (space_hit: Z) (sep: Z) (PreH1 : (n = (string_length (str_l)))) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (w = 0)) (PreH5 : (out_size = 0)) (PreH6 : (start = (-1))) (PreH7 : (ch = 0)) (PreH8 : (len = 0)) (PreH9 : (space_hit = 0)) (PreH10 : (comma_hit <> 0)) (PreH11 : ((contains_zb_125 (str_l) (32)) = false)) (PreH12 : ((contains_zb_125 (str_l) (44)) = true)) (PreH13 : (sep = 44)) (PreH14 : (valid_string str_l )) (PreH15 : (all_ascii str_l )) (PreH16 : (valid_split_words_input_125 str_l )) (PreH17 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH18 : (problem_125_pre_z str_l )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string txt_pre str_l )
  **  (PtrArray.undef_full data (n + 1 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_words_safety_wit_30 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (i >= n)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (0 <= out_size)) (PreH8 : (out_size <= i)) (PreH9 : (out_size = (Zlength (output_rows)))) (PreH10 : ((Zlength (output_ptrs)) = out_size)) (PreH11 : ((-1) <= start)) (PreH12 : (start < i)) (PreH13 : (sep = 44)) (PreH14 : (sep = 32)) (PreH15 : ((contains_zb_125 (str_l) (32)) = true)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= len)) (PreH19 : (len < INT_MAX)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_split_words_input_125 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_125_pre_z str_l )) (PreH25 : (split_scan_state_125 str_l i start sep output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ False ”
.

Definition split_words_safety_wit_31 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (i < n)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (0 <= out_size)) (PreH8 : (out_size <= i)) (PreH9 : (out_size = (Zlength (output_rows)))) (PreH10 : ((Zlength (output_ptrs)) = out_size)) (PreH11 : ((-1) <= start)) (PreH12 : (start < i)) (PreH13 : (sep = 44)) (PreH14 : (sep = 32)) (PreH15 : ((contains_zb_125 (str_l) (32)) = true)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= len)) (PreH19 : (len < INT_MAX)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_split_words_input_125 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_125_pre_z str_l )) (PreH25 : (split_scan_state_125 str_l i start sep output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ False ”
.

Definition split_words_safety_wit_32 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (i >= n)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (0 <= out_size)) (PreH8 : (out_size <= i)) (PreH9 : (out_size = (Zlength (output_rows)))) (PreH10 : ((Zlength (output_ptrs)) = out_size)) (PreH11 : ((-1) <= start)) (PreH12 : (start < i)) (PreH13 : (sep = 32)) (PreH14 : (sep = 44)) (PreH15 : ((contains_zb_125 (str_l) (32)) = false)) (PreH16 : ((contains_zb_125 (str_l) (44)) = true)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_split_words_input_125 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_125_pre_z str_l )) (PreH26 : (split_scan_state_125 str_l i start sep output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ False ”
.

Definition split_words_safety_wit_33 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (i < n)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (0 <= out_size)) (PreH8 : (out_size <= i)) (PreH9 : (out_size = (Zlength (output_rows)))) (PreH10 : ((Zlength (output_ptrs)) = out_size)) (PreH11 : ((-1) <= start)) (PreH12 : (start < i)) (PreH13 : (sep = 32)) (PreH14 : (sep = 44)) (PreH15 : ((contains_zb_125 (str_l) (32)) = false)) (PreH16 : ((contains_zb_125 (str_l) (44)) = true)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_split_words_input_125 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_125_pre_z str_l )) (PreH26 : (split_scan_state_125 str_l i start sep output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ False ”
.

Definition split_words_safety_wit_34 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) = sep)) (PreH2 : (i < n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : ((-1) <= start)) (PreH13 : (start < i)) (PreH14 : (sep = 44)) (PreH15 : (sep = 44)) (PreH16 : ((contains_zb_125 (str_l) (32)) = false)) (PreH17 : ((contains_zb_125 (str_l) (44)) = true)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_split_words_input_125 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_125_pre_z str_l )) (PreH27 : (split_scan_state_125 str_l i start sep output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_words_safety_wit_35 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) = sep)) (PreH2 : (i < n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : ((-1) <= start)) (PreH13 : (start < i)) (PreH14 : (sep = 32)) (PreH15 : (sep = 32)) (PreH16 : ((contains_zb_125 (str_l) (32)) = true)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_split_words_input_125 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_125_pre_z str_l )) (PreH26 : (split_scan_state_125 str_l i start sep output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_words_safety_wit_36 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = sep)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (sep = 44)) (PreH16 : (sep = 44)) (PreH17 : ((contains_zb_125 (str_l) (32)) = false)) (PreH18 : ((contains_zb_125 (str_l) (44)) = true)) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : (0 <= len)) (PreH22 : (len < INT_MAX)) (PreH23 : (valid_string str_l )) (PreH24 : (all_ascii str_l )) (PreH25 : (valid_split_words_input_125 str_l )) (PreH26 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH27 : (problem_125_pre_z str_l )) (PreH28 : (split_scan_state_125 str_l i start sep output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ ((i - start ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - start )) ”
.

Definition split_words_safety_wit_37 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = sep)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (sep = 32)) (PreH16 : (sep = 32)) (PreH17 : ((contains_zb_125 (str_l) (32)) = true)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_split_words_input_125 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_125_pre_z str_l )) (PreH27 : (split_scan_state_125 str_l i start sep output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ ((i - start ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - start )) ”
.

Definition split_words_safety_wit_38 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = sep)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (sep = 44)) (PreH16 : (sep = 44)) (PreH17 : ((contains_zb_125 (str_l) (32)) = false)) (PreH18 : ((contains_zb_125 (str_l) (44)) = true)) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : (0 <= len)) (PreH22 : (len < INT_MAX)) (PreH23 : (valid_string str_l )) (PreH24 : (all_ascii str_l )) (PreH25 : (valid_split_words_input_125 str_l )) (PreH26 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH27 : (problem_125_pre_z str_l )) (PreH28 : (split_scan_state_125 str_l i start sep output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> (i - start ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ (((i - start ) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((i - start ) + 1 )) ”
.

Definition split_words_safety_wit_39 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = sep)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (sep = 44)) (PreH16 : (sep = 44)) (PreH17 : ((contains_zb_125 (str_l) (32)) = false)) (PreH18 : ((contains_zb_125 (str_l) (44)) = true)) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : (0 <= len)) (PreH22 : (len < INT_MAX)) (PreH23 : (valid_string str_l )) (PreH24 : (all_ascii str_l )) (PreH25 : (valid_split_words_input_125 str_l )) (PreH26 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH27 : (problem_125_pre_z str_l )) (PreH28 : (split_scan_state_125 str_l i start sep output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> (i - start ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition split_words_safety_wit_40 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = sep)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (sep = 32)) (PreH16 : (sep = 32)) (PreH17 : ((contains_zb_125 (str_l) (32)) = true)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_split_words_input_125 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_125_pre_z str_l )) (PreH27 : (split_scan_state_125 str_l i start sep output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> (i - start ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ (((i - start ) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((i - start ) + 1 )) ”
.

Definition split_words_safety_wit_41 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = sep)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (sep = 32)) (PreH16 : (sep = 32)) (PreH17 : ((contains_zb_125 (str_l) (32)) = true)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_split_words_input_125 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_125_pre_z str_l )) (PreH27 : (split_scan_state_125 str_l i start sep output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> (i - start ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition split_words_safety_wit_42 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (start >= 0)) (PreH4 : ((Znth i (c_string (str_l)) 0) = sep)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_rows)))) (PreH14 : ((Zlength (output_ptrs)) = out_size)) (PreH15 : ((-1) <= start)) (PreH16 : (start < i)) (PreH17 : (sep = 44)) (PreH18 : (sep = 44)) (PreH19 : ((contains_zb_125 (str_l) (32)) = false)) (PreH20 : ((contains_zb_125 (str_l) (44)) = true)) (PreH21 : (0 <= ch)) (PreH22 : (ch <= 127)) (PreH23 : (0 <= len)) (PreH24 : (len < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_split_words_input_125 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_125_pre_z str_l )) (PreH30 : (split_scan_state_125 str_l i start sep output_rows )) ,
  ((( &( "k" ) )) # Int  |->_)
  **  (CharArray.undef_full retval ((i - start ) + 1 ) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> retval)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> (i - start ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_words_safety_wit_43 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (start >= 0)) (PreH4 : ((Znth i (c_string (str_l)) 0) = sep)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_rows)))) (PreH14 : ((Zlength (output_ptrs)) = out_size)) (PreH15 : ((-1) <= start)) (PreH16 : (start < i)) (PreH17 : (sep = 32)) (PreH18 : (sep = 32)) (PreH19 : ((contains_zb_125 (str_l) (32)) = true)) (PreH20 : (0 <= ch)) (PreH21 : (ch <= 127)) (PreH22 : (0 <= len)) (PreH23 : (len < INT_MAX)) (PreH24 : (valid_string str_l )) (PreH25 : (all_ascii str_l )) (PreH26 : (valid_split_words_input_125 str_l )) (PreH27 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH28 : (problem_125_pre_z str_l )) (PreH29 : (split_scan_state_125 str_l i start sep output_rows )) ,
  ((( &( "k" ) )) # Int  |->_)
  **  (CharArray.undef_full retval ((i - start ) + 1 ) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> retval)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> (i - start ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_words_safety_wit_44 :=
forall (txt_pre: Z) (str_l: (@list Z)) (k: Z) (sep: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (k >= len)) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (0 <= start)) (PreH13 : (start < i)) (PreH14 : (len = (i - start ))) (PreH15 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH16 : (ch = sep)) (PreH17 : (sep = 44)) (PreH18 : (sep = 32)) (PreH19 : ((contains_zb_125 (str_l) (32)) = true)) (PreH20 : (0 <= ch)) (PreH21 : (ch <= 127)) (PreH22 : (0 <= k)) (PreH23 : (k <= len)) (PreH24 : (valid_string str_l )) (PreH25 : (all_ascii str_l )) (PreH26 : (valid_split_words_input_125 str_l )) (PreH27 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH28 : (problem_125_pre_z str_l )) (PreH29 : (split_scan_state_125 str_l i start sep output_rows )) (PreH30 : ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i)))) (PreH31 : ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_125 (str_l) (start) ((start + k ))) )
  **  (CharArray.undef_seg w k (len + 1 ) )
|--
  “ False ”
.

Definition split_words_safety_wit_45 :=
forall (txt_pre: Z) (str_l: (@list Z)) (k: Z) (sep: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (k < len)) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (0 <= start)) (PreH13 : (start < i)) (PreH14 : (len = (i - start ))) (PreH15 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH16 : (ch = sep)) (PreH17 : (sep = 44)) (PreH18 : (sep = 32)) (PreH19 : ((contains_zb_125 (str_l) (32)) = true)) (PreH20 : (0 <= ch)) (PreH21 : (ch <= 127)) (PreH22 : (0 <= k)) (PreH23 : (k <= len)) (PreH24 : (valid_string str_l )) (PreH25 : (all_ascii str_l )) (PreH26 : (valid_split_words_input_125 str_l )) (PreH27 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH28 : (problem_125_pre_z str_l )) (PreH29 : (split_scan_state_125 str_l i start sep output_rows )) (PreH30 : ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i)))) (PreH31 : ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_125 (str_l) (start) ((start + k ))) )
  **  (CharArray.undef_seg w k (len + 1 ) )
|--
  “ False ”
.

Definition split_words_safety_wit_46 :=
forall (txt_pre: Z) (str_l: (@list Z)) (k: Z) (sep: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (k >= len)) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (0 <= start)) (PreH13 : (start < i)) (PreH14 : (len = (i - start ))) (PreH15 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH16 : (ch = sep)) (PreH17 : (sep = 32)) (PreH18 : (sep = 44)) (PreH19 : ((contains_zb_125 (str_l) (32)) = false)) (PreH20 : ((contains_zb_125 (str_l) (44)) = true)) (PreH21 : (0 <= ch)) (PreH22 : (ch <= 127)) (PreH23 : (0 <= k)) (PreH24 : (k <= len)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_split_words_input_125 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_125_pre_z str_l )) (PreH30 : (split_scan_state_125 str_l i start sep output_rows )) (PreH31 : ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i)))) (PreH32 : ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_125 (str_l) (start) ((start + k ))) )
  **  (CharArray.undef_seg w k (len + 1 ) )
|--
  “ False ”
.

Definition split_words_safety_wit_47 :=
forall (txt_pre: Z) (str_l: (@list Z)) (k: Z) (sep: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (k < len)) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (0 <= start)) (PreH13 : (start < i)) (PreH14 : (len = (i - start ))) (PreH15 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH16 : (ch = sep)) (PreH17 : (sep = 32)) (PreH18 : (sep = 44)) (PreH19 : ((contains_zb_125 (str_l) (32)) = false)) (PreH20 : ((contains_zb_125 (str_l) (44)) = true)) (PreH21 : (0 <= ch)) (PreH22 : (ch <= 127)) (PreH23 : (0 <= k)) (PreH24 : (k <= len)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_split_words_input_125 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_125_pre_z str_l )) (PreH30 : (split_scan_state_125 str_l i start sep output_rows )) (PreH31 : ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i)))) (PreH32 : ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_125 (str_l) (start) ((start + k ))) )
  **  (CharArray.undef_seg w k (len + 1 ) )
|--
  “ False ”
.

Definition split_words_safety_wit_48 :=
forall (txt_pre: Z) (str_l: (@list Z)) (k: Z) (sep: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (k < len)) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (0 <= start)) (PreH13 : (start < i)) (PreH14 : (len = (i - start ))) (PreH15 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH16 : (ch = sep)) (PreH17 : (sep = 44)) (PreH18 : (sep = 44)) (PreH19 : ((contains_zb_125 (str_l) (32)) = false)) (PreH20 : ((contains_zb_125 (str_l) (44)) = true)) (PreH21 : (0 <= ch)) (PreH22 : (ch <= 127)) (PreH23 : (0 <= k)) (PreH24 : (k <= len)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_split_words_input_125 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_125_pre_z str_l )) (PreH30 : (split_scan_state_125 str_l i start sep output_rows )) (PreH31 : ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i)))) (PreH32 : ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_125 (str_l) (start) ((start + k ))) )
  **  (CharArray.undef_seg w k (len + 1 ) )
|--
  “ ((start + k ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (start + k )) ”
.

Definition split_words_safety_wit_49 :=
forall (txt_pre: Z) (str_l: (@list Z)) (k: Z) (sep: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (k < len)) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (0 <= start)) (PreH13 : (start < i)) (PreH14 : (len = (i - start ))) (PreH15 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH16 : (ch = sep)) (PreH17 : (sep = 32)) (PreH18 : (sep = 32)) (PreH19 : ((contains_zb_125 (str_l) (32)) = true)) (PreH20 : (0 <= ch)) (PreH21 : (ch <= 127)) (PreH22 : (0 <= k)) (PreH23 : (k <= len)) (PreH24 : (valid_string str_l )) (PreH25 : (all_ascii str_l )) (PreH26 : (valid_split_words_input_125 str_l )) (PreH27 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH28 : (problem_125_pre_z str_l )) (PreH29 : (split_scan_state_125 str_l i start sep output_rows )) (PreH30 : ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i)))) (PreH31 : ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_125 (str_l) (start) ((start + k ))) )
  **  (CharArray.undef_seg w k (len + 1 ) )
|--
  “ ((start + k ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (start + k )) ”
.

Definition split_words_safety_wit_50 :=
forall (txt_pre: Z) (str_l: (@list Z)) (k: Z) (sep: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (k < len)) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (w <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : (0 <= start)) (PreH14 : (start < i)) (PreH15 : (len = (i - start ))) (PreH16 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH17 : (ch = sep)) (PreH18 : (sep = 44)) (PreH19 : (sep = 44)) (PreH20 : ((contains_zb_125 (str_l) (32)) = false)) (PreH21 : ((contains_zb_125 (str_l) (44)) = true)) (PreH22 : (0 <= ch)) (PreH23 : (ch <= 127)) (PreH24 : (0 <= k)) (PreH25 : (k <= len)) (PreH26 : (valid_string str_l )) (PreH27 : (all_ascii str_l )) (PreH28 : (valid_split_words_input_125 str_l )) (PreH29 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH30 : (problem_125_pre_z str_l )) (PreH31 : (split_scan_state_125 str_l i start sep output_rows )) (PreH32 : ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i)))) (PreH33 : ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len)) ,
  (CharArray.full w (k + 1 ) (app ((word_payload_125 (str_l) (start) ((start + k )))) ((cons ((Znth (start + k ) (c_string (str_l)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg w (k + 1 ) (len + 1 ) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ ((k + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition split_words_safety_wit_51 :=
forall (txt_pre: Z) (str_l: (@list Z)) (k: Z) (sep: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (k < len)) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (w <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : (0 <= start)) (PreH14 : (start < i)) (PreH15 : (len = (i - start ))) (PreH16 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH17 : (ch = sep)) (PreH18 : (sep = 32)) (PreH19 : (sep = 32)) (PreH20 : ((contains_zb_125 (str_l) (32)) = true)) (PreH21 : (0 <= ch)) (PreH22 : (ch <= 127)) (PreH23 : (0 <= k)) (PreH24 : (k <= len)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_split_words_input_125 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_125_pre_z str_l )) (PreH30 : (split_scan_state_125 str_l i start sep output_rows )) (PreH31 : ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i)))) (PreH32 : ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len)) ,
  (CharArray.full w (k + 1 ) (app ((word_payload_125 (str_l) (start) ((start + k )))) ((cons ((Znth (start + k ) (c_string (str_l)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg w (k + 1 ) (len + 1 ) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ ((k + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition split_words_safety_wit_52 :=
forall (txt_pre: Z) (str_l: (@list Z)) (k: Z) (sep: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (k >= len)) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (0 <= start)) (PreH13 : (start < i)) (PreH14 : (len = (i - start ))) (PreH15 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH16 : (ch = sep)) (PreH17 : (sep = 44)) (PreH18 : (sep = 44)) (PreH19 : ((contains_zb_125 (str_l) (32)) = false)) (PreH20 : ((contains_zb_125 (str_l) (44)) = true)) (PreH21 : (0 <= ch)) (PreH22 : (ch <= 127)) (PreH23 : (0 <= k)) (PreH24 : (k <= len)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_split_words_input_125 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_125_pre_z str_l )) (PreH30 : (split_scan_state_125 str_l i start sep output_rows )) (PreH31 : ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i)))) (PreH32 : ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_125 (str_l) (start) ((start + k ))) )
  **  (CharArray.undef_seg w k (len + 1 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_words_safety_wit_53 :=
forall (txt_pre: Z) (str_l: (@list Z)) (k: Z) (sep: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (k >= len)) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (0 <= start)) (PreH13 : (start < i)) (PreH14 : (len = (i - start ))) (PreH15 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH16 : (ch = sep)) (PreH17 : (sep = 32)) (PreH18 : (sep = 32)) (PreH19 : ((contains_zb_125 (str_l) (32)) = true)) (PreH20 : (0 <= ch)) (PreH21 : (ch <= 127)) (PreH22 : (0 <= k)) (PreH23 : (k <= len)) (PreH24 : (valid_string str_l )) (PreH25 : (all_ascii str_l )) (PreH26 : (valid_split_words_input_125 str_l )) (PreH27 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH28 : (problem_125_pre_z str_l )) (PreH29 : (split_scan_state_125 str_l i start sep output_rows )) (PreH30 : ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i)))) (PreH31 : ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_125 (str_l) (start) ((start + k ))) )
  **  (CharArray.undef_seg w k (len + 1 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_words_safety_wit_54 :=
forall (txt_pre: Z) (str_l: (@list Z)) (k: Z) (sep: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (k >= len)) (PreH4 : (0 <= i)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (w <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : (0 <= start)) (PreH15 : (start < i)) (PreH16 : (len = (i - start ))) (PreH17 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH18 : (ch = sep)) (PreH19 : (sep = 44)) (PreH20 : (sep = 44)) (PreH21 : ((contains_zb_125 (str_l) (32)) = false)) (PreH22 : ((contains_zb_125 (str_l) (44)) = true)) (PreH23 : (0 <= ch)) (PreH24 : (ch <= 127)) (PreH25 : (0 <= k)) (PreH26 : (k <= len)) (PreH27 : (valid_string str_l )) (PreH28 : (all_ascii str_l )) (PreH29 : (valid_split_words_input_125 str_l )) (PreH30 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH31 : (problem_125_pre_z str_l )) (PreH32 : (split_scan_state_125 str_l i start sep output_rows )) (PreH33 : ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i)))) (PreH34 : ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len)) ,
  (PtrArray.seg data 0 (out_size + 1 ) (app (output_ptrs) ((cons (w) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full w (k + 1 ) (app ((word_payload_125 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ ((out_size + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (out_size + 1 )) ”
.

Definition split_words_safety_wit_55 :=
forall (txt_pre: Z) (str_l: (@list Z)) (k: Z) (sep: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (k >= len)) (PreH4 : (0 <= i)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (w <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : (0 <= start)) (PreH15 : (start < i)) (PreH16 : (len = (i - start ))) (PreH17 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH18 : (ch = sep)) (PreH19 : (sep = 32)) (PreH20 : (sep = 32)) (PreH21 : ((contains_zb_125 (str_l) (32)) = true)) (PreH22 : (0 <= ch)) (PreH23 : (ch <= 127)) (PreH24 : (0 <= k)) (PreH25 : (k <= len)) (PreH26 : (valid_string str_l )) (PreH27 : (all_ascii str_l )) (PreH28 : (valid_split_words_input_125 str_l )) (PreH29 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH30 : (problem_125_pre_z str_l )) (PreH31 : (split_scan_state_125 str_l i start sep output_rows )) (PreH32 : ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i)))) (PreH33 : ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len)) ,
  (PtrArray.seg data 0 (out_size + 1 ) (app (output_ptrs) ((cons (w) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full w (k + 1 ) (app ((word_payload_125 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ ((out_size + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (out_size + 1 )) ”
.

Definition split_words_safety_wit_56 :=
forall (txt_pre: Z) (str_l: (@list Z)) (k: Z) (sep: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (k >= len)) (PreH4 : (0 <= i)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (w <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : (0 <= start)) (PreH15 : (start < i)) (PreH16 : (len = (i - start ))) (PreH17 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH18 : (ch = sep)) (PreH19 : (sep = 44)) (PreH20 : (sep = 44)) (PreH21 : ((contains_zb_125 (str_l) (32)) = false)) (PreH22 : ((contains_zb_125 (str_l) (44)) = true)) (PreH23 : (0 <= ch)) (PreH24 : (ch <= 127)) (PreH25 : (0 <= k)) (PreH26 : (k <= len)) (PreH27 : (valid_string str_l )) (PreH28 : (all_ascii str_l )) (PreH29 : (valid_split_words_input_125 str_l )) (PreH30 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH31 : (problem_125_pre_z str_l )) (PreH32 : (split_scan_state_125 str_l i start sep output_rows )) (PreH33 : ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i)))) (PreH34 : ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len)) ,
  (PtrArray.seg data 0 (out_size + 1 ) (app (output_ptrs) ((cons (w) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full w (k + 1 ) (app ((word_payload_125 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> (out_size + 1 ))
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition split_words_safety_wit_57 :=
forall (txt_pre: Z) (str_l: (@list Z)) (k: Z) (sep: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (k >= len)) (PreH4 : (0 <= i)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (w <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : (0 <= start)) (PreH15 : (start < i)) (PreH16 : (len = (i - start ))) (PreH17 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH18 : (ch = sep)) (PreH19 : (sep = 44)) (PreH20 : (sep = 44)) (PreH21 : ((contains_zb_125 (str_l) (32)) = false)) (PreH22 : ((contains_zb_125 (str_l) (44)) = true)) (PreH23 : (0 <= ch)) (PreH24 : (ch <= 127)) (PreH25 : (0 <= k)) (PreH26 : (k <= len)) (PreH27 : (valid_string str_l )) (PreH28 : (all_ascii str_l )) (PreH29 : (valid_split_words_input_125 str_l )) (PreH30 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH31 : (problem_125_pre_z str_l )) (PreH32 : (split_scan_state_125 str_l i start sep output_rows )) (PreH33 : ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i)))) (PreH34 : ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len)) ,
  (PtrArray.seg data 0 (out_size + 1 ) (app (output_ptrs) ((cons (w) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full w (k + 1 ) (app ((word_payload_125 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> (out_size + 1 ))
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition split_words_safety_wit_58 :=
forall (txt_pre: Z) (str_l: (@list Z)) (k: Z) (sep: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (k >= len)) (PreH4 : (0 <= i)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (w <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : (0 <= start)) (PreH15 : (start < i)) (PreH16 : (len = (i - start ))) (PreH17 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH18 : (ch = sep)) (PreH19 : (sep = 32)) (PreH20 : (sep = 32)) (PreH21 : ((contains_zb_125 (str_l) (32)) = true)) (PreH22 : (0 <= ch)) (PreH23 : (ch <= 127)) (PreH24 : (0 <= k)) (PreH25 : (k <= len)) (PreH26 : (valid_string str_l )) (PreH27 : (all_ascii str_l )) (PreH28 : (valid_split_words_input_125 str_l )) (PreH29 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH30 : (problem_125_pre_z str_l )) (PreH31 : (split_scan_state_125 str_l i start sep output_rows )) (PreH32 : ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i)))) (PreH33 : ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len)) ,
  (PtrArray.seg data 0 (out_size + 1 ) (app (output_ptrs) ((cons (w) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full w (k + 1 ) (app ((word_payload_125 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> (out_size + 1 ))
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition split_words_safety_wit_59 :=
forall (txt_pre: Z) (str_l: (@list Z)) (k: Z) (sep: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (k >= len)) (PreH4 : (0 <= i)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (w <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : (0 <= start)) (PreH15 : (start < i)) (PreH16 : (len = (i - start ))) (PreH17 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH18 : (ch = sep)) (PreH19 : (sep = 32)) (PreH20 : (sep = 32)) (PreH21 : ((contains_zb_125 (str_l) (32)) = true)) (PreH22 : (0 <= ch)) (PreH23 : (ch <= 127)) (PreH24 : (0 <= k)) (PreH25 : (k <= len)) (PreH26 : (valid_string str_l )) (PreH27 : (all_ascii str_l )) (PreH28 : (valid_split_words_input_125 str_l )) (PreH29 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH30 : (problem_125_pre_z str_l )) (PreH31 : (split_scan_state_125 str_l i start sep output_rows )) (PreH32 : ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i)))) (PreH33 : ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len)) ,
  (PtrArray.seg data 0 (out_size + 1 ) (app (output_ptrs) ((cons (w) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full w (k + 1 ) (app ((word_payload_125 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> (out_size + 1 ))
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition split_words_safety_wit_60 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) <> sep)) (PreH2 : (i < n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : ((-1) <= start)) (PreH13 : (start < i)) (PreH14 : (sep = 44)) (PreH15 : (sep = 44)) (PreH16 : ((contains_zb_125 (str_l) (32)) = false)) (PreH17 : ((contains_zb_125 (str_l) (44)) = true)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_split_words_input_125 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_125_pre_z str_l )) (PreH27 : (split_scan_state_125 str_l i start sep output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_words_safety_wit_61 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) <> sep)) (PreH2 : (i < n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : ((-1) <= start)) (PreH13 : (start < i)) (PreH14 : (sep = 32)) (PreH15 : (sep = 32)) (PreH16 : ((contains_zb_125 (str_l) (32)) = true)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_split_words_input_125 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_125_pre_z str_l )) (PreH26 : (split_scan_state_125 str_l i start sep output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_words_safety_wit_62 :=
forall (txt_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (w: Z) (comma_hit: Z) (space_hit: Z) (out_size: Z) (start: Z) (ch: Z) (sep: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (w <> 0)) (PreH7 : (0 <= out_size)) (PreH8 : (out_size <= (i + 1 ))) (PreH9 : (out_size = (Zlength (output_rows)))) (PreH10 : ((Zlength (output_ptrs)) = out_size)) (PreH11 : (start = (-1))) (PreH12 : (ch = sep)) (PreH13 : (sep = 44)) (PreH14 : (sep = 32)) (PreH15 : ((contains_zb_125 (str_l) (32)) = true)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= len)) (PreH19 : (len < INT_MAX)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_split_words_input_125 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_125_pre_z str_l )) (PreH25 : (split_scan_state_125 str_l (i + 1 ) start sep output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition split_words_safety_wit_63 :=
forall (txt_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (w: Z) (comma_hit: Z) (space_hit: Z) (out_size: Z) (start: Z) (ch: Z) (sep: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (w <> 0)) (PreH7 : (0 <= out_size)) (PreH8 : (out_size <= (i + 1 ))) (PreH9 : (out_size = (Zlength (output_rows)))) (PreH10 : ((Zlength (output_ptrs)) = out_size)) (PreH11 : (start = (-1))) (PreH12 : (ch = sep)) (PreH13 : (sep = 44)) (PreH14 : (sep = 44)) (PreH15 : ((contains_zb_125 (str_l) (32)) = false)) (PreH16 : ((contains_zb_125 (str_l) (44)) = true)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_split_words_input_125 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_125_pre_z str_l )) (PreH26 : (split_scan_state_125 str_l (i + 1 ) start sep output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition split_words_safety_wit_64 :=
forall (txt_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (w: Z) (comma_hit: Z) (space_hit: Z) (out_size: Z) (start: Z) (ch: Z) (sep: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (w <> 0)) (PreH7 : (0 <= out_size)) (PreH8 : (out_size <= (i + 1 ))) (PreH9 : (out_size = (Zlength (output_rows)))) (PreH10 : ((Zlength (output_ptrs)) = out_size)) (PreH11 : (start = (-1))) (PreH12 : (ch = sep)) (PreH13 : (sep = 32)) (PreH14 : (sep = 32)) (PreH15 : ((contains_zb_125 (str_l) (32)) = true)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= len)) (PreH19 : (len < INT_MAX)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_split_words_input_125 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_125_pre_z str_l )) (PreH25 : (split_scan_state_125 str_l (i + 1 ) start sep output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition split_words_safety_wit_65 :=
forall (txt_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (w: Z) (comma_hit: Z) (space_hit: Z) (out_size: Z) (start: Z) (ch: Z) (sep: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (w <> 0)) (PreH7 : (0 <= out_size)) (PreH8 : (out_size <= (i + 1 ))) (PreH9 : (out_size = (Zlength (output_rows)))) (PreH10 : ((Zlength (output_ptrs)) = out_size)) (PreH11 : (start = (-1))) (PreH12 : (ch = sep)) (PreH13 : (sep = 32)) (PreH14 : (sep = 44)) (PreH15 : ((contains_zb_125 (str_l) (32)) = false)) (PreH16 : ((contains_zb_125 (str_l) (44)) = true)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_split_words_input_125 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_125_pre_z str_l )) (PreH26 : (split_scan_state_125 str_l (i + 1 ) start sep output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition split_words_safety_wit_66 :=
forall (txt_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (w: Z) (comma_hit: Z) (space_hit: Z) (out_size: Z) (start: Z) (ch: Z) (sep: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= out_size)) (PreH7 : (out_size <= i)) (PreH8 : (out_size = (Zlength (output_rows)))) (PreH9 : ((Zlength (output_ptrs)) = out_size)) (PreH10 : (start = (-1))) (PreH11 : (ch = sep)) (PreH12 : (sep = 44)) (PreH13 : (sep = 32)) (PreH14 : ((contains_zb_125 (str_l) (32)) = true)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= len)) (PreH18 : (len < INT_MAX)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_split_words_input_125 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_125_pre_z str_l )) (PreH24 : (split_scan_state_125 str_l (i + 1 ) start sep output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition split_words_safety_wit_67 :=
forall (txt_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (w: Z) (comma_hit: Z) (space_hit: Z) (out_size: Z) (start: Z) (ch: Z) (sep: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= out_size)) (PreH7 : (out_size <= i)) (PreH8 : (out_size = (Zlength (output_rows)))) (PreH9 : ((Zlength (output_ptrs)) = out_size)) (PreH10 : (start = (-1))) (PreH11 : (ch = sep)) (PreH12 : (sep = 44)) (PreH13 : (sep = 44)) (PreH14 : ((contains_zb_125 (str_l) (32)) = false)) (PreH15 : ((contains_zb_125 (str_l) (44)) = true)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= len)) (PreH19 : (len < INT_MAX)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_split_words_input_125 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_125_pre_z str_l )) (PreH25 : (split_scan_state_125 str_l (i + 1 ) start sep output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition split_words_safety_wit_68 :=
forall (txt_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (w: Z) (comma_hit: Z) (space_hit: Z) (out_size: Z) (start: Z) (ch: Z) (sep: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= out_size)) (PreH7 : (out_size <= i)) (PreH8 : (out_size = (Zlength (output_rows)))) (PreH9 : ((Zlength (output_ptrs)) = out_size)) (PreH10 : (start = (-1))) (PreH11 : (ch = sep)) (PreH12 : (sep = 32)) (PreH13 : (sep = 32)) (PreH14 : ((contains_zb_125 (str_l) (32)) = true)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= len)) (PreH18 : (len < INT_MAX)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_split_words_input_125 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_125_pre_z str_l )) (PreH24 : (split_scan_state_125 str_l (i + 1 ) start sep output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition split_words_safety_wit_69 :=
forall (txt_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (w: Z) (comma_hit: Z) (space_hit: Z) (out_size: Z) (start: Z) (ch: Z) (sep: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= out_size)) (PreH7 : (out_size <= i)) (PreH8 : (out_size = (Zlength (output_rows)))) (PreH9 : ((Zlength (output_ptrs)) = out_size)) (PreH10 : (start = (-1))) (PreH11 : (ch = sep)) (PreH12 : (sep = 32)) (PreH13 : (sep = 44)) (PreH14 : ((contains_zb_125 (str_l) (32)) = false)) (PreH15 : ((contains_zb_125 (str_l) (44)) = true)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= len)) (PreH19 : (len < INT_MAX)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_split_words_input_125 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_125_pre_z str_l )) (PreH25 : (split_scan_state_125 str_l (i + 1 ) start sep output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition split_words_safety_wit_70 :=
forall (txt_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (w: Z) (comma_hit: Z) (space_hit: Z) (out_size: Z) (start: Z) (ch: Z) (sep: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= out_size)) (PreH7 : (out_size <= i)) (PreH8 : (out_size = (Zlength (output_rows)))) (PreH9 : ((Zlength (output_ptrs)) = out_size)) (PreH10 : (0 <= start)) (PreH11 : (start <= i)) (PreH12 : (ch <> sep)) (PreH13 : (sep = 44)) (PreH14 : (sep = 32)) (PreH15 : ((contains_zb_125 (str_l) (32)) = true)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= len)) (PreH19 : (len < INT_MAX)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_split_words_input_125 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_125_pre_z str_l )) (PreH25 : (split_scan_state_125 str_l (i + 1 ) start sep output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition split_words_safety_wit_71 :=
forall (txt_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (w: Z) (comma_hit: Z) (space_hit: Z) (out_size: Z) (start: Z) (ch: Z) (sep: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= out_size)) (PreH7 : (out_size <= i)) (PreH8 : (out_size = (Zlength (output_rows)))) (PreH9 : ((Zlength (output_ptrs)) = out_size)) (PreH10 : (0 <= start)) (PreH11 : (start <= i)) (PreH12 : (ch <> sep)) (PreH13 : (sep = 44)) (PreH14 : (sep = 44)) (PreH15 : ((contains_zb_125 (str_l) (32)) = false)) (PreH16 : ((contains_zb_125 (str_l) (44)) = true)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_split_words_input_125 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_125_pre_z str_l )) (PreH26 : (split_scan_state_125 str_l (i + 1 ) start sep output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition split_words_safety_wit_72 :=
forall (txt_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (w: Z) (comma_hit: Z) (space_hit: Z) (out_size: Z) (start: Z) (ch: Z) (sep: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= out_size)) (PreH7 : (out_size <= i)) (PreH8 : (out_size = (Zlength (output_rows)))) (PreH9 : ((Zlength (output_ptrs)) = out_size)) (PreH10 : (0 <= start)) (PreH11 : (start <= i)) (PreH12 : (ch <> sep)) (PreH13 : (sep = 32)) (PreH14 : (sep = 32)) (PreH15 : ((contains_zb_125 (str_l) (32)) = true)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= len)) (PreH19 : (len < INT_MAX)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_split_words_input_125 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_125_pre_z str_l )) (PreH25 : (split_scan_state_125 str_l (i + 1 ) start sep output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition split_words_safety_wit_73 :=
forall (txt_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (w: Z) (comma_hit: Z) (space_hit: Z) (out_size: Z) (start: Z) (ch: Z) (sep: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= out_size)) (PreH7 : (out_size <= i)) (PreH8 : (out_size = (Zlength (output_rows)))) (PreH9 : ((Zlength (output_ptrs)) = out_size)) (PreH10 : (0 <= start)) (PreH11 : (start <= i)) (PreH12 : (ch <> sep)) (PreH13 : (sep = 32)) (PreH14 : (sep = 44)) (PreH15 : ((contains_zb_125 (str_l) (32)) = false)) (PreH16 : ((contains_zb_125 (str_l) (44)) = true)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_split_words_input_125 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_125_pre_z str_l )) (PreH26 : (split_scan_state_125 str_l (i + 1 ) start sep output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition split_words_safety_wit_74 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (i >= n)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (0 <= out_size)) (PreH8 : (out_size <= i)) (PreH9 : (out_size = (Zlength (output_rows)))) (PreH10 : ((Zlength (output_ptrs)) = out_size)) (PreH11 : ((-1) <= start)) (PreH12 : (start < i)) (PreH13 : (sep = 44)) (PreH14 : (sep = 44)) (PreH15 : ((contains_zb_125 (str_l) (32)) = false)) (PreH16 : ((contains_zb_125 (str_l) (44)) = true)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_split_words_input_125 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_125_pre_z str_l )) (PreH26 : (split_scan_state_125 str_l i start sep output_rows )) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_words_safety_wit_75 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (i >= n)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (0 <= out_size)) (PreH8 : (out_size <= i)) (PreH9 : (out_size = (Zlength (output_rows)))) (PreH10 : ((Zlength (output_ptrs)) = out_size)) (PreH11 : ((-1) <= start)) (PreH12 : (start < i)) (PreH13 : (sep = 32)) (PreH14 : (sep = 32)) (PreH15 : ((contains_zb_125 (str_l) (32)) = true)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= len)) (PreH19 : (len < INT_MAX)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_split_words_input_125 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_125_pre_z str_l )) (PreH25 : (split_scan_state_125 str_l i start sep output_rows )) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_words_safety_wit_76 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : (i >= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : ((-1) <= start)) (PreH13 : (start < i)) (PreH14 : (sep = 44)) (PreH15 : (sep = 44)) (PreH16 : ((contains_zb_125 (str_l) (32)) = false)) (PreH17 : ((contains_zb_125 (str_l) (44)) = true)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_split_words_input_125 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_125_pre_z str_l )) (PreH27 : (split_scan_state_125 str_l i start sep output_rows )) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ ((n - start ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n - start )) ”
.

Definition split_words_safety_wit_77 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : (i >= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : ((-1) <= start)) (PreH13 : (start < i)) (PreH14 : (sep = 32)) (PreH15 : (sep = 32)) (PreH16 : ((contains_zb_125 (str_l) (32)) = true)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_split_words_input_125 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_125_pre_z str_l )) (PreH26 : (split_scan_state_125 str_l i start sep output_rows )) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ ((n - start ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n - start )) ”
.

Definition split_words_safety_wit_78 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : (i >= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : ((-1) <= start)) (PreH13 : (start < i)) (PreH14 : (sep = 44)) (PreH15 : (sep = 44)) (PreH16 : ((contains_zb_125 (str_l) (32)) = false)) (PreH17 : ((contains_zb_125 (str_l) (44)) = true)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_split_words_input_125 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_125_pre_z str_l )) (PreH27 : (split_scan_state_125 str_l i start sep output_rows )) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "len" ) )) # Int  |-> (n - start ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ (((n - start ) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((n - start ) + 1 )) ”
.

Definition split_words_safety_wit_79 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : (i >= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : ((-1) <= start)) (PreH13 : (start < i)) (PreH14 : (sep = 44)) (PreH15 : (sep = 44)) (PreH16 : ((contains_zb_125 (str_l) (32)) = false)) (PreH17 : ((contains_zb_125 (str_l) (44)) = true)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_split_words_input_125 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_125_pre_z str_l )) (PreH27 : (split_scan_state_125 str_l i start sep output_rows )) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "len" ) )) # Int  |-> (n - start ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition split_words_safety_wit_80 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : (i >= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : ((-1) <= start)) (PreH13 : (start < i)) (PreH14 : (sep = 32)) (PreH15 : (sep = 32)) (PreH16 : ((contains_zb_125 (str_l) (32)) = true)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_split_words_input_125 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_125_pre_z str_l )) (PreH26 : (split_scan_state_125 str_l i start sep output_rows )) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "len" ) )) # Int  |-> (n - start ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ (((n - start ) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((n - start ) + 1 )) ”
.

Definition split_words_safety_wit_81 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : (i >= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : ((-1) <= start)) (PreH13 : (start < i)) (PreH14 : (sep = 32)) (PreH15 : (sep = 32)) (PreH16 : ((contains_zb_125 (str_l) (32)) = true)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_split_words_input_125 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_125_pre_z str_l )) (PreH26 : (split_scan_state_125 str_l i start sep output_rows )) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "len" ) )) # Int  |-> (n - start ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition split_words_safety_wit_82 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (start >= 0)) (PreH4 : (i >= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : ((-1) <= start)) (PreH15 : (start < i)) (PreH16 : (sep = 44)) (PreH17 : (sep = 44)) (PreH18 : ((contains_zb_125 (str_l) (32)) = false)) (PreH19 : ((contains_zb_125 (str_l) (44)) = true)) (PreH20 : (0 <= ch)) (PreH21 : (ch <= 127)) (PreH22 : (0 <= len)) (PreH23 : (len < INT_MAX)) (PreH24 : (valid_string str_l )) (PreH25 : (all_ascii str_l )) (PreH26 : (valid_split_words_input_125 str_l )) (PreH27 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH28 : (problem_125_pre_z str_l )) (PreH29 : (split_scan_state_125 str_l i start sep output_rows )) ,
  ((( &( "k" ) )) # Int  |->_)
  **  (CharArray.undef_full retval ((n - start ) + 1 ) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> retval)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "len" ) )) # Int  |-> (n - start ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_words_safety_wit_83 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (space_hit: Z) (comma_hit: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (start >= 0)) (PreH4 : (i >= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : ((-1) <= start)) (PreH15 : (start < i)) (PreH16 : (sep = 32)) (PreH17 : (sep = 32)) (PreH18 : ((contains_zb_125 (str_l) (32)) = true)) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : (0 <= len)) (PreH22 : (len < INT_MAX)) (PreH23 : (valid_string str_l )) (PreH24 : (all_ascii str_l )) (PreH25 : (valid_split_words_input_125 str_l )) (PreH26 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH27 : (problem_125_pre_z str_l )) (PreH28 : (split_scan_state_125 str_l i start sep output_rows )) ,
  ((( &( "k" ) )) # Int  |->_)
  **  (CharArray.undef_full retval ((n - start ) + 1 ) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> retval)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "len" ) )) # Int  |-> (n - start ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_words_safety_wit_84 :=
forall (txt_pre: Z) (str_l: (@list Z)) (sep: Z) (k: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (ch: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (k >= len)) (PreH2 : (n = (string_length (str_l)))) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (w <> 0)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= n)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (0 <= start)) (PreH13 : (start < n)) (PreH14 : (len = (n - start ))) (PreH15 : (0 <= k)) (PreH16 : (k <= len)) (PreH17 : (sep = 44)) (PreH18 : (sep = 32)) (PreH19 : ((contains_zb_125 (str_l) (32)) = true)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_split_words_input_125 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_125_pre_z str_l )) (PreH25 : (split_scan_state_125 str_l n start sep output_rows )) (PreH26 : ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n)))) (PreH27 : ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len)) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_125 (str_l) (start) ((start + k ))) )
  **  (CharArray.undef_seg w k (len + 1 ) )
|--
  “ False ”
.

Definition split_words_safety_wit_85 :=
forall (txt_pre: Z) (str_l: (@list Z)) (sep: Z) (k: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (ch: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (k < len)) (PreH2 : (n = (string_length (str_l)))) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (w <> 0)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= n)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (0 <= start)) (PreH13 : (start < n)) (PreH14 : (len = (n - start ))) (PreH15 : (0 <= k)) (PreH16 : (k <= len)) (PreH17 : (sep = 44)) (PreH18 : (sep = 32)) (PreH19 : ((contains_zb_125 (str_l) (32)) = true)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_split_words_input_125 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_125_pre_z str_l )) (PreH25 : (split_scan_state_125 str_l n start sep output_rows )) (PreH26 : ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n)))) (PreH27 : ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len)) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_125 (str_l) (start) ((start + k ))) )
  **  (CharArray.undef_seg w k (len + 1 ) )
|--
  “ False ”
.

Definition split_words_safety_wit_86 :=
forall (txt_pre: Z) (str_l: (@list Z)) (sep: Z) (k: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (ch: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (k >= len)) (PreH2 : (n = (string_length (str_l)))) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (w <> 0)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= n)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (0 <= start)) (PreH13 : (start < n)) (PreH14 : (len = (n - start ))) (PreH15 : (0 <= k)) (PreH16 : (k <= len)) (PreH17 : (sep = 32)) (PreH18 : (sep = 44)) (PreH19 : ((contains_zb_125 (str_l) (32)) = false)) (PreH20 : ((contains_zb_125 (str_l) (44)) = true)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_split_words_input_125 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_125_pre_z str_l )) (PreH26 : (split_scan_state_125 str_l n start sep output_rows )) (PreH27 : ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n)))) (PreH28 : ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len)) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_125 (str_l) (start) ((start + k ))) )
  **  (CharArray.undef_seg w k (len + 1 ) )
|--
  “ False ”
.

Definition split_words_safety_wit_87 :=
forall (txt_pre: Z) (str_l: (@list Z)) (sep: Z) (k: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (ch: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (k < len)) (PreH2 : (n = (string_length (str_l)))) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (w <> 0)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= n)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (0 <= start)) (PreH13 : (start < n)) (PreH14 : (len = (n - start ))) (PreH15 : (0 <= k)) (PreH16 : (k <= len)) (PreH17 : (sep = 32)) (PreH18 : (sep = 44)) (PreH19 : ((contains_zb_125 (str_l) (32)) = false)) (PreH20 : ((contains_zb_125 (str_l) (44)) = true)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_split_words_input_125 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_125_pre_z str_l )) (PreH26 : (split_scan_state_125 str_l n start sep output_rows )) (PreH27 : ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n)))) (PreH28 : ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len)) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_125 (str_l) (start) ((start + k ))) )
  **  (CharArray.undef_seg w k (len + 1 ) )
|--
  “ False ”
.

Definition split_words_safety_wit_88 :=
forall (txt_pre: Z) (str_l: (@list Z)) (sep: Z) (k: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (ch: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (k < len)) (PreH2 : (n = (string_length (str_l)))) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (w <> 0)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= n)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (0 <= start)) (PreH13 : (start < n)) (PreH14 : (len = (n - start ))) (PreH15 : (0 <= k)) (PreH16 : (k <= len)) (PreH17 : (sep = 44)) (PreH18 : (sep = 44)) (PreH19 : ((contains_zb_125 (str_l) (32)) = false)) (PreH20 : ((contains_zb_125 (str_l) (44)) = true)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_split_words_input_125 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_125_pre_z str_l )) (PreH26 : (split_scan_state_125 str_l n start sep output_rows )) (PreH27 : ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n)))) (PreH28 : ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len)) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_125 (str_l) (start) ((start + k ))) )
  **  (CharArray.undef_seg w k (len + 1 ) )
|--
  “ ((start + k ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (start + k )) ”
.

Definition split_words_safety_wit_89 :=
forall (txt_pre: Z) (str_l: (@list Z)) (sep: Z) (k: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (ch: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (k < len)) (PreH2 : (n = (string_length (str_l)))) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (w <> 0)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= n)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (0 <= start)) (PreH13 : (start < n)) (PreH14 : (len = (n - start ))) (PreH15 : (0 <= k)) (PreH16 : (k <= len)) (PreH17 : (sep = 32)) (PreH18 : (sep = 32)) (PreH19 : ((contains_zb_125 (str_l) (32)) = true)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_split_words_input_125 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_125_pre_z str_l )) (PreH25 : (split_scan_state_125 str_l n start sep output_rows )) (PreH26 : ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n)))) (PreH27 : ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len)) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_125 (str_l) (start) ((start + k ))) )
  **  (CharArray.undef_seg w k (len + 1 ) )
|--
  “ ((start + k ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (start + k )) ”
.

Definition split_words_safety_wit_90 :=
forall (txt_pre: Z) (str_l: (@list Z)) (sep: Z) (k: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (ch: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (k < len)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (w <> 0)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= n)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : (0 <= start)) (PreH14 : (start < n)) (PreH15 : (len = (n - start ))) (PreH16 : (0 <= k)) (PreH17 : (k <= len)) (PreH18 : (sep = 44)) (PreH19 : (sep = 44)) (PreH20 : ((contains_zb_125 (str_l) (32)) = false)) (PreH21 : ((contains_zb_125 (str_l) (44)) = true)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_split_words_input_125 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_125_pre_z str_l )) (PreH27 : (split_scan_state_125 str_l n start sep output_rows )) (PreH28 : ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n)))) (PreH29 : ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len)) ,
  (CharArray.full w (k + 1 ) (app ((word_payload_125 (str_l) (start) ((start + k )))) ((cons ((Znth (start + k ) (c_string (str_l)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg w (k + 1 ) (len + 1 ) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ ((k + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition split_words_safety_wit_91 :=
forall (txt_pre: Z) (str_l: (@list Z)) (sep: Z) (k: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (ch: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (k < len)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (w <> 0)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= n)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : (0 <= start)) (PreH14 : (start < n)) (PreH15 : (len = (n - start ))) (PreH16 : (0 <= k)) (PreH17 : (k <= len)) (PreH18 : (sep = 32)) (PreH19 : (sep = 32)) (PreH20 : ((contains_zb_125 (str_l) (32)) = true)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_split_words_input_125 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_125_pre_z str_l )) (PreH26 : (split_scan_state_125 str_l n start sep output_rows )) (PreH27 : ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n)))) (PreH28 : ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len)) ,
  (CharArray.full w (k + 1 ) (app ((word_payload_125 (str_l) (start) ((start + k )))) ((cons ((Znth (start + k ) (c_string (str_l)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg w (k + 1 ) (len + 1 ) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ ((k + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition split_words_safety_wit_92 :=
forall (txt_pre: Z) (str_l: (@list Z)) (sep: Z) (k: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (ch: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (k >= len)) (PreH2 : (n = (string_length (str_l)))) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (w <> 0)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= n)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (0 <= start)) (PreH13 : (start < n)) (PreH14 : (len = (n - start ))) (PreH15 : (0 <= k)) (PreH16 : (k <= len)) (PreH17 : (sep = 44)) (PreH18 : (sep = 44)) (PreH19 : ((contains_zb_125 (str_l) (32)) = false)) (PreH20 : ((contains_zb_125 (str_l) (44)) = true)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_split_words_input_125 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_125_pre_z str_l )) (PreH26 : (split_scan_state_125 str_l n start sep output_rows )) (PreH27 : ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n)))) (PreH28 : ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len)) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_125 (str_l) (start) ((start + k ))) )
  **  (CharArray.undef_seg w k (len + 1 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_words_safety_wit_93 :=
forall (txt_pre: Z) (str_l: (@list Z)) (sep: Z) (k: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (ch: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (k >= len)) (PreH2 : (n = (string_length (str_l)))) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (w <> 0)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= n)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (0 <= start)) (PreH13 : (start < n)) (PreH14 : (len = (n - start ))) (PreH15 : (0 <= k)) (PreH16 : (k <= len)) (PreH17 : (sep = 32)) (PreH18 : (sep = 32)) (PreH19 : ((contains_zb_125 (str_l) (32)) = true)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_split_words_input_125 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_125_pre_z str_l )) (PreH25 : (split_scan_state_125 str_l n start sep output_rows )) (PreH26 : ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n)))) (PreH27 : ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len)) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_125 (str_l) (start) ((start + k ))) )
  **  (CharArray.undef_seg w k (len + 1 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_words_safety_wit_94 :=
forall (txt_pre: Z) (str_l: (@list Z)) (sep: Z) (k: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (ch: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (k >= len)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= n)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : (0 <= start)) (PreH15 : (start < n)) (PreH16 : (len = (n - start ))) (PreH17 : (0 <= k)) (PreH18 : (k <= len)) (PreH19 : (sep = 44)) (PreH20 : (sep = 44)) (PreH21 : ((contains_zb_125 (str_l) (32)) = false)) (PreH22 : ((contains_zb_125 (str_l) (44)) = true)) (PreH23 : (valid_string str_l )) (PreH24 : (all_ascii str_l )) (PreH25 : (valid_split_words_input_125 str_l )) (PreH26 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH27 : (problem_125_pre_z str_l )) (PreH28 : (split_scan_state_125 str_l n start sep output_rows )) (PreH29 : ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n)))) (PreH30 : ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len)) ,
  (PtrArray.seg data 0 (out_size + 1 ) (app (output_ptrs) ((cons (w) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full w (k + 1 ) (app ((word_payload_125 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ ((out_size + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (out_size + 1 )) ”
.

Definition split_words_safety_wit_95 :=
forall (txt_pre: Z) (str_l: (@list Z)) (sep: Z) (k: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (ch: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (k >= len)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= n)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : (0 <= start)) (PreH15 : (start < n)) (PreH16 : (len = (n - start ))) (PreH17 : (0 <= k)) (PreH18 : (k <= len)) (PreH19 : (sep = 32)) (PreH20 : (sep = 32)) (PreH21 : ((contains_zb_125 (str_l) (32)) = true)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_split_words_input_125 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_125_pre_z str_l )) (PreH27 : (split_scan_state_125 str_l n start sep output_rows )) (PreH28 : ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n)))) (PreH29 : ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len)) ,
  (PtrArray.seg data 0 (out_size + 1 ) (app (output_ptrs) ((cons (w) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full w (k + 1 ) (app ((word_payload_125 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ ((out_size + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (out_size + 1 )) ”
.

Definition split_words_safety_wit_96 :=
forall (txt_pre: Z) (str_l: (@list Z)) (sep: Z) (k: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (ch: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (k >= len)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= n)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : (0 <= start)) (PreH15 : (start < n)) (PreH16 : (len = (n - start ))) (PreH17 : (0 <= k)) (PreH18 : (k <= len)) (PreH19 : (sep = 44)) (PreH20 : (sep = 44)) (PreH21 : ((contains_zb_125 (str_l) (32)) = false)) (PreH22 : ((contains_zb_125 (str_l) (44)) = true)) (PreH23 : (valid_string str_l )) (PreH24 : (all_ascii str_l )) (PreH25 : (valid_split_words_input_125 str_l )) (PreH26 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH27 : (problem_125_pre_z str_l )) (PreH28 : (split_scan_state_125 str_l n start sep output_rows )) (PreH29 : ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n)))) (PreH30 : ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len)) ,
  (PtrArray.seg data 0 (out_size + 1 ) (app (output_ptrs) ((cons (w) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full w (k + 1 ) (app ((word_payload_125 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "out_size" ) )) # Int  |-> (out_size + 1 ))
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition split_words_safety_wit_97 :=
forall (txt_pre: Z) (str_l: (@list Z)) (sep: Z) (k: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (ch: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (k >= len)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= n)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : (0 <= start)) (PreH15 : (start < n)) (PreH16 : (len = (n - start ))) (PreH17 : (0 <= k)) (PreH18 : (k <= len)) (PreH19 : (sep = 44)) (PreH20 : (sep = 44)) (PreH21 : ((contains_zb_125 (str_l) (32)) = false)) (PreH22 : ((contains_zb_125 (str_l) (44)) = true)) (PreH23 : (valid_string str_l )) (PreH24 : (all_ascii str_l )) (PreH25 : (valid_split_words_input_125 str_l )) (PreH26 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH27 : (problem_125_pre_z str_l )) (PreH28 : (split_scan_state_125 str_l n start sep output_rows )) (PreH29 : ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n)))) (PreH30 : ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len)) ,
  (PtrArray.seg data 0 (out_size + 1 ) (app (output_ptrs) ((cons (w) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full w (k + 1 ) (app ((word_payload_125 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "out_size" ) )) # Int  |-> (out_size + 1 ))
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition split_words_safety_wit_98 :=
forall (txt_pre: Z) (str_l: (@list Z)) (sep: Z) (k: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (ch: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (k >= len)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= n)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : (0 <= start)) (PreH15 : (start < n)) (PreH16 : (len = (n - start ))) (PreH17 : (0 <= k)) (PreH18 : (k <= len)) (PreH19 : (sep = 32)) (PreH20 : (sep = 32)) (PreH21 : ((contains_zb_125 (str_l) (32)) = true)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_split_words_input_125 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_125_pre_z str_l )) (PreH27 : (split_scan_state_125 str_l n start sep output_rows )) (PreH28 : ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n)))) (PreH29 : ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len)) ,
  (PtrArray.seg data 0 (out_size + 1 ) (app (output_ptrs) ((cons (w) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full w (k + 1 ) (app ((word_payload_125 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "out_size" ) )) # Int  |-> (out_size + 1 ))
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition split_words_safety_wit_99 :=
forall (txt_pre: Z) (str_l: (@list Z)) (sep: Z) (k: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (ch: Z) (space_hit: Z) (comma_hit: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (k >= len)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= n)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : (0 <= start)) (PreH15 : (start < n)) (PreH16 : (len = (n - start ))) (PreH17 : (0 <= k)) (PreH18 : (k <= len)) (PreH19 : (sep = 32)) (PreH20 : (sep = 32)) (PreH21 : ((contains_zb_125 (str_l) (32)) = true)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_split_words_input_125 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_125_pre_z str_l )) (PreH27 : (split_scan_state_125 str_l n start sep output_rows )) (PreH28 : ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n)))) (PreH29 : ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len)) ,
  (PtrArray.seg data 0 (out_size + 1 ) (app (output_ptrs) ((cons (w) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full w (k + 1 ) (app ((word_payload_125 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "out_size" ) )) # Int  |-> (out_size + 1 ))
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "sep" ) )) # Int  |-> sep)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition split_words_safety_wit_100 :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_2 = 0)) (PreH3 : (retval_5 <> 0)) (PreH4 : (retval_4 <> 0)) (PreH5 : (strchr_result str_l 44 retval_3 txt_pre )) (PreH6 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH7 : (retval = (string_length (str_l)))) (PreH8 : (0 <= ((string_length (str_l)) + 1 ))) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (valid_split_words_input_125 str_l )) (PreH12 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH13 : (problem_125_pre_z str_l )) ,
  ((( &( "out_size" ) )) # Int  |->_)
  **  (PtrArray.undef_full retval_5 (retval + 1 ) )
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_5)
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "comma_hit" ) )) # Ptr  |-> retval_3)
  **  ((( &( "space_hit" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "data" ) )) # Ptr  |-> retval_5)
  **  ((( &( "out" ) )) # Ptr  |-> retval_4)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_words_safety_wit_101 :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_2 = 0)) (PreH3 : (retval_5 <> 0)) (PreH4 : (retval_4 <> 0)) (PreH5 : (strchr_result str_l 44 retval_3 txt_pre )) (PreH6 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH7 : (retval = (string_length (str_l)))) (PreH8 : (0 <= ((string_length (str_l)) + 1 ))) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (valid_split_words_input_125 str_l )) (PreH12 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH13 : (problem_125_pre_z str_l )) ,
  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  (PtrArray.undef_full retval_5 (retval + 1 ) )
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_5)
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "comma_hit" ) )) # Ptr  |-> retval_3)
  **  ((( &( "space_hit" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "data" ) )) # Ptr  |-> retval_5)
  **  ((( &( "out" ) )) # Ptr  |-> retval_4)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_words_safety_wit_102 :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_2 = 0)) (PreH3 : (retval_5 <> 0)) (PreH4 : (retval_4 <> 0)) (PreH5 : (strchr_result str_l 44 retval_3 txt_pre )) (PreH6 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH7 : (retval = (string_length (str_l)))) (PreH8 : (0 <= ((string_length (str_l)) + 1 ))) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (valid_split_words_input_125 str_l )) (PreH12 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH13 : (problem_125_pre_z str_l )) ,
  ((( &( "w" ) )) # Ptr  |->_)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  (PtrArray.undef_full retval_5 (retval + 1 ) )
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_5)
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "comma_hit" ) )) # Ptr  |-> retval_3)
  **  ((( &( "space_hit" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "data" ) )) # Ptr  |-> retval_5)
  **  ((( &( "out" ) )) # Ptr  |-> retval_4)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_words_safety_wit_103 :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_2 = 0)) (PreH3 : (retval_5 <> 0)) (PreH4 : (retval_4 <> 0)) (PreH5 : (strchr_result str_l 44 retval_3 txt_pre )) (PreH6 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH7 : (retval = (string_length (str_l)))) (PreH8 : (0 <= ((string_length (str_l)) + 1 ))) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (valid_split_words_input_125 str_l )) (PreH12 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH13 : (problem_125_pre_z str_l )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "w" ) )) # Ptr  |-> 0)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  (PtrArray.undef_full retval_5 (retval + 1 ) )
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_5)
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "comma_hit" ) )) # Ptr  |-> retval_3)
  **  ((( &( "space_hit" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "data" ) )) # Ptr  |-> retval_5)
  **  ((( &( "out" ) )) # Ptr  |-> retval_4)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_words_safety_wit_104 :=
forall (txt_pre: Z) (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (i < n)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (0 <= len)) (PreH11 : (len < INT_MAX)) (PreH12 : (space_hit = 0)) (PreH13 : (comma_hit = 0)) (PreH14 : ((contains_zb_125 (str_l) (32)) = false)) (PreH15 : ((contains_zb_125 (str_l) (44)) = false)) (PreH16 : (valid_string str_l )) (PreH17 : (all_ascii str_l )) (PreH18 : (valid_split_words_input_125 str_l )) (PreH19 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH20 : (problem_125_pre_z str_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string txt_pre str_l )
  **  (PtrArray.undef_full data (n + 1 ) )
|--
  “ (97 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 97) ”
.

Definition split_words_safety_wit_105 :=
forall (txt_pre: Z) (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) >= 97)) (PreH2 : (i < n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (0 <= len)) (PreH12 : (len < INT_MAX)) (PreH13 : (space_hit = 0)) (PreH14 : (comma_hit = 0)) (PreH15 : ((contains_zb_125 (str_l) (32)) = false)) (PreH16 : ((contains_zb_125 (str_l) (44)) = false)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (valid_split_words_input_125 str_l )) (PreH20 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH21 : (problem_125_pre_z str_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string txt_pre str_l )
  **  (PtrArray.undef_full data (n + 1 ) )
|--
  “ (122 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 122) ”
.

Definition split_words_safety_wit_106 :=
forall (txt_pre: Z) (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) <= 122)) (PreH2 : ((Znth i (c_string (str_l)) 0) >= 97)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (0 <= len)) (PreH13 : (len < INT_MAX)) (PreH14 : (space_hit = 0)) (PreH15 : (comma_hit = 0)) (PreH16 : ((contains_zb_125 (str_l) (32)) = false)) (PreH17 : ((contains_zb_125 (str_l) (44)) = false)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (valid_split_words_input_125 str_l )) (PreH21 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH22 : (problem_125_pre_z str_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string txt_pre str_l )
  **  (PtrArray.undef_full data (n + 1 ) )
|--
  “ (((Znth i (c_string (str_l)) 0) <> (INT_MIN)) \/ (2 <> (-1))) ”
  &&  “ (2 <> 0) ”
.

Definition split_words_safety_wit_107 :=
forall (txt_pre: Z) (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) <= 122)) (PreH2 : ((Znth i (c_string (str_l)) 0) >= 97)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (0 <= len)) (PreH13 : (len < INT_MAX)) (PreH14 : (space_hit = 0)) (PreH15 : (comma_hit = 0)) (PreH16 : ((contains_zb_125 (str_l) (32)) = false)) (PreH17 : ((contains_zb_125 (str_l) (44)) = false)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (valid_split_words_input_125 str_l )) (PreH21 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH22 : (problem_125_pre_z str_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string txt_pre str_l )
  **  (PtrArray.undef_full data (n + 1 ) )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition split_words_safety_wit_108 :=
forall (txt_pre: Z) (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) <= 122)) (PreH2 : ((Znth i (c_string (str_l)) 0) >= 97)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (0 <= len)) (PreH13 : (len < INT_MAX)) (PreH14 : (space_hit = 0)) (PreH15 : (comma_hit = 0)) (PreH16 : ((contains_zb_125 (str_l) (32)) = false)) (PreH17 : ((contains_zb_125 (str_l) (44)) = false)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (valid_split_words_input_125 str_l )) (PreH21 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH22 : (problem_125_pre_z str_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string txt_pre str_l )
  **  (PtrArray.undef_full data (n + 1 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_words_safety_wit_109 :=
forall (txt_pre: Z) (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (((Znth i (c_string (str_l)) 0) % ( 2 ) ) = 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) <= 122)) (PreH3 : ((Znth i (c_string (str_l)) 0) >= 97)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (0 <= len)) (PreH14 : (len < INT_MAX)) (PreH15 : (space_hit = 0)) (PreH16 : (comma_hit = 0)) (PreH17 : ((contains_zb_125 (str_l) (32)) = false)) (PreH18 : ((contains_zb_125 (str_l) (44)) = false)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_split_words_input_125 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_125_pre_z str_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string txt_pre str_l )
  **  (PtrArray.undef_full data (n + 1 ) )
|--
  “ ((out_size + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (out_size + 1 )) ”
.

Definition split_words_safety_wit_110 :=
forall (txt_pre: Z) (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (((Znth i (c_string (str_l)) 0) % ( 2 ) ) = 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) <= 122)) (PreH3 : ((Znth i (c_string (str_l)) 0) >= 97)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (0 <= len)) (PreH14 : (len < INT_MAX)) (PreH15 : (space_hit = 0)) (PreH16 : (comma_hit = 0)) (PreH17 : ((contains_zb_125 (str_l) (32)) = false)) (PreH18 : ((contains_zb_125 (str_l) (44)) = false)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_split_words_input_125 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_125_pre_z str_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string txt_pre str_l )
  **  (PtrArray.undef_full data (n + 1 ) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition split_words_safety_wit_111 :=
forall (txt_pre: Z) (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (((Znth i (c_string (str_l)) 0) % ( 2 ) ) = 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) <= 122)) (PreH3 : ((Znth i (c_string (str_l)) 0) >= 97)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (0 <= len)) (PreH14 : (len < INT_MAX)) (PreH15 : (space_hit = 0)) (PreH16 : (comma_hit = 0)) (PreH17 : ((contains_zb_125 (str_l) (32)) = false)) (PreH18 : ((contains_zb_125 (str_l) (44)) = false)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_split_words_input_125 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_125_pre_z str_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> (out_size + 1 ))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string txt_pre str_l )
  **  (PtrArray.undef_full data (n + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition split_words_safety_wit_112 :=
forall (txt_pre: Z) (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) > 122)) (PreH2 : ((Znth i (c_string (str_l)) 0) >= 97)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (0 <= len)) (PreH13 : (len < INT_MAX)) (PreH14 : (space_hit = 0)) (PreH15 : (comma_hit = 0)) (PreH16 : ((contains_zb_125 (str_l) (32)) = false)) (PreH17 : ((contains_zb_125 (str_l) (44)) = false)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (valid_split_words_input_125 str_l )) (PreH21 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH22 : (problem_125_pre_z str_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string txt_pre str_l )
  **  (PtrArray.undef_full data (n + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition split_words_safety_wit_113 :=
forall (txt_pre: Z) (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) < 97)) (PreH2 : (i < n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (0 <= len)) (PreH12 : (len < INT_MAX)) (PreH13 : (space_hit = 0)) (PreH14 : (comma_hit = 0)) (PreH15 : ((contains_zb_125 (str_l) (32)) = false)) (PreH16 : ((contains_zb_125 (str_l) (44)) = false)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (valid_split_words_input_125 str_l )) (PreH20 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH21 : (problem_125_pre_z str_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string txt_pre str_l )
  **  (PtrArray.undef_full data (n + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition split_words_safety_wit_114 :=
forall (txt_pre: Z) (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (((Znth i (c_string (str_l)) 0) % ( 2 ) ) <> 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) <= 122)) (PreH3 : ((Znth i (c_string (str_l)) 0) >= 97)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (0 <= len)) (PreH14 : (len < INT_MAX)) (PreH15 : (space_hit = 0)) (PreH16 : (comma_hit = 0)) (PreH17 : ((contains_zb_125 (str_l) (32)) = false)) (PreH18 : ((contains_zb_125 (str_l) (44)) = false)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_split_words_input_125 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_125_pre_z str_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string txt_pre str_l )
  **  (PtrArray.undef_full data (n + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition split_words_safety_wit_115 :=
forall (txt_pre: Z) (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (1 <= retval)) (PreH2 : (retval < INT_MAX)) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (i >= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (0 <= len)) (PreH14 : (len < INT_MAX)) (PreH15 : (space_hit = 0)) (PreH16 : (comma_hit = 0)) (PreH17 : ((contains_zb_125 (str_l) (32)) = false)) (PreH18 : ((contains_zb_125 (str_l) (44)) = false)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_split_words_input_125 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_125_pre_z str_l )) ,
  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (PtrArray.undef_full data (n + 1 ) )
|--
  “ ((retval + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition split_words_safety_wit_116 :=
forall (txt_pre: Z) (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (1 <= retval)) (PreH2 : (retval < INT_MAX)) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (i >= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (0 <= len)) (PreH14 : (len < INT_MAX)) (PreH15 : (space_hit = 0)) (PreH16 : (comma_hit = 0)) (PreH17 : ((contains_zb_125 (str_l) (32)) = false)) (PreH18 : ((contains_zb_125 (str_l) (44)) = false)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_split_words_input_125 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_125_pre_z str_l )) ,
  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (PtrArray.undef_full data (n + 1 ) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition split_words_safety_wit_117 :=
forall (txt_pre: Z) (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (retval_2: Z) (out_l: (@list Z)) (PreH1 : ((Zlength (out_l)) = retval)) (PreH2 : (retval_2 <> 0)) (PreH3 : (1 <= retval)) (PreH4 : (retval < INT_MAX)) (PreH5 : (0 <= ((string_length (str_l)) + 1 ))) (PreH6 : (i >= n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (n = (string_length (str_l)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH13 : (0 <= out_size)) (PreH14 : (out_size <= i)) (PreH15 : (0 <= len)) (PreH16 : (len < INT_MAX)) (PreH17 : (space_hit = 0)) (PreH18 : (comma_hit = 0)) (PreH19 : ((contains_zb_125 (str_l) (32)) = false)) (PreH20 : ((contains_zb_125 (str_l) (44)) = false)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_split_words_input_125 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_125_pre_z str_l )) ,
  (CharArray.full retval_2 (retval + 1 ) (c_string (out_l)) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> retval_2)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (PtrArray.undef_full data (n + 1 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_words_safety_wit_118 :=
forall (txt_pre: Z) (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (retval_2: Z) (out_l: (@list Z)) (PreH1 : (0 <= (retval + 1 ))) (PreH2 : ((Zlength (out_l)) = retval)) (PreH3 : (retval_2 <> 0)) (PreH4 : (1 <= retval)) (PreH5 : (retval < INT_MAX)) (PreH6 : (0 <= ((string_length (str_l)) + 1 ))) (PreH7 : (i >= n)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (n = (string_length (str_l)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH14 : (0 <= out_size)) (PreH15 : (out_size <= i)) (PreH16 : (0 <= len)) (PreH17 : (len < INT_MAX)) (PreH18 : (space_hit = 0)) (PreH19 : (comma_hit = 0)) (PreH20 : ((contains_zb_125 (str_l) (32)) = false)) (PreH21 : ((contains_zb_125 (str_l) (44)) = false)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_split_words_input_125 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_125_pre_z str_l )) ,
  (((data + (0 * sizeof(PTR) ) )) # Ptr  |-> retval_2)
  **  (PtrArray.undef_missing_i data 0 0 (n + 1 ) )
  **  (CharArray.full retval_2 (retval + 1 ) (c_string (out_l)) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> retval_2)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition split_words_entail_wit_1_1 :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_5: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_5 <> 0)) (PreH3 : (retval_2 = 0)) (PreH4 : (retval_4 <> 0)) (PreH5 : (retval_3 <> 0)) (PreH6 : (strchr_result str_l 44 retval_5 txt_pre )) (PreH7 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH8 : (retval = (string_length (str_l)))) (PreH9 : (0 <= ((string_length (str_l)) + 1 ))) (PreH10 : (valid_string str_l )) (PreH11 : (all_ascii str_l )) (PreH12 : (valid_split_words_input_125 str_l )) (PreH13 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH14 : (problem_125_pre_z str_l )) ,
  (PtrArray.undef_full retval_4 (retval + 1 ) )
  **  ((&((retval_3)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_4)
  **  ((&((retval_3)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
|--
  (“ (retval = (string_length (str_l))) ”
  &&  “ (retval_3 <> 0) ”
  &&  “ (retval_4 <> 0) ”
  &&  “ (0 = 0) ”
  &&  “ (0 = 0) ”
  &&  “ ((-1) = (-1)) ”
  &&  “ (0 = 0) ”
  &&  “ (0 = 0) ”
  &&  “ (retval_2 <> 0) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (44 = 32) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  ((&((retval_3)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_4)
  **  ((&((retval_3)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string txt_pre str_l )
  **  (PtrArray.undef_full retval_4 (retval + 1 ) ))
  ||
  (“ (retval = (string_length (str_l))) ”
  &&  “ (retval_3 <> 0) ”
  &&  “ (retval_4 <> 0) ”
  &&  “ (0 = 0) ”
  &&  “ (0 = 0) ”
  &&  “ ((-1) = (-1)) ”
  &&  “ (0 = 0) ”
  &&  “ (0 = 0) ”
  &&  “ (retval_2 = 0) ”
  &&  “ (retval_5 <> 0) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (44 = 44) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  ((&((retval_3)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_4)
  **  ((&((retval_3)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string txt_pre str_l )
  **  (PtrArray.undef_full retval_4 (retval + 1 ) ))
.

Definition split_words_entail_wit_1_2 :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_5: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_4 <> 0)) (PreH4 : (retval_3 <> 0)) (PreH5 : (strchr_result str_l 44 retval_5 txt_pre )) (PreH6 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH7 : (retval = (string_length (str_l)))) (PreH8 : (0 <= ((string_length (str_l)) + 1 ))) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (valid_split_words_input_125 str_l )) (PreH12 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH13 : (problem_125_pre_z str_l )) ,
  (PtrArray.undef_full retval_4 (retval + 1 ) )
  **  ((&((retval_3)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_4)
  **  ((&((retval_3)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
|--
  (“ (retval = (string_length (str_l))) ”
  &&  “ (retval_3 <> 0) ”
  &&  “ (retval_4 <> 0) ”
  &&  “ (0 = 0) ”
  &&  “ (0 = 0) ”
  &&  “ ((-1) = (-1)) ”
  &&  “ (0 = 0) ”
  &&  “ (0 = 0) ”
  &&  “ (retval_2 <> 0) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (32 = 32) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  ((&((retval_3)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_4)
  **  ((&((retval_3)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string txt_pre str_l )
  **  (PtrArray.undef_full retval_4 (retval + 1 ) ))
  ||
  (“ (retval = (string_length (str_l))) ”
  &&  “ (retval_3 <> 0) ”
  &&  “ (retval_4 <> 0) ”
  &&  “ (0 = 0) ”
  &&  “ (0 = 0) ”
  &&  “ ((-1) = (-1)) ”
  &&  “ (0 = 0) ”
  &&  “ (0 = 0) ”
  &&  “ (retval_2 = 0) ”
  &&  “ (retval_5 <> 0) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (32 = 44) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  ((&((retval_3)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_4)
  **  ((&((retval_3)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string txt_pre str_l )
  **  (PtrArray.undef_full retval_4 (retval + 1 ) ))
.

Definition split_words_entail_wit_2_1 :=
forall (txt_pre: Z) (str_l: (@list Z)) (n: Z) (out: Z) (data: Z) (w: Z) (out_size: Z) (start: Z) (ch: Z) (len: Z) (space_hit: Z) (sep: Z) (PreH1 : (n = (string_length (str_l)))) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (w = 0)) (PreH5 : (out_size = 0)) (PreH6 : (start = (-1))) (PreH7 : (ch = 0)) (PreH8 : (len = 0)) (PreH9 : (space_hit <> 0)) (PreH10 : ((contains_zb_125 (str_l) (32)) = true)) (PreH11 : (sep = 32)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (valid_split_words_input_125 str_l )) (PreH15 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH16 : (problem_125_pre_z str_l )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string txt_pre str_l )
  **  (PtrArray.undef_full data (n + 1 ) )
|--
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= 0) ”
  &&  “ (0 <= n) ”
  &&  “ (n = (string_length (str_l))) ”
  &&  “ (out <> 0) ”
  &&  “ (data <> 0) ”
  &&  “ (0 <= out_size) ”
  &&  “ (out_size <= 0) ”
  &&  “ (out_size = (Zlength (output_rows))) ”
  &&  “ ((Zlength (output_ptrs)) = out_size) ”
  &&  “ ((-1) <= start) ”
  &&  “ (start < 0) ”
  &&  “ (sep = 44) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l 0 start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= 0) ”
  &&  “ (0 <= n) ”
  &&  “ (n = (string_length (str_l))) ”
  &&  “ (out <> 0) ”
  &&  “ (data <> 0) ”
  &&  “ (0 <= out_size) ”
  &&  “ (out_size <= 0) ”
  &&  “ (out_size = (Zlength (output_rows))) ”
  &&  “ ((Zlength (output_ptrs)) = out_size) ”
  &&  “ ((-1) <= start) ”
  &&  “ (start < 0) ”
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l 0 start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= 0) ”
  &&  “ (0 <= n) ”
  &&  “ (n = (string_length (str_l))) ”
  &&  “ (out <> 0) ”
  &&  “ (data <> 0) ”
  &&  “ (0 <= out_size) ”
  &&  “ (out_size <= 0) ”
  &&  “ (out_size = (Zlength (output_rows))) ”
  &&  “ ((Zlength (output_ptrs)) = out_size) ”
  &&  “ ((-1) <= start) ”
  &&  “ (start < 0) ”
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l 0 start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= 0) ”
  &&  “ (0 <= n) ”
  &&  “ (n = (string_length (str_l))) ”
  &&  “ (out <> 0) ”
  &&  “ (data <> 0) ”
  &&  “ (0 <= out_size) ”
  &&  “ (out_size <= 0) ”
  &&  “ (out_size = (Zlength (output_rows))) ”
  &&  “ ((Zlength (output_ptrs)) = out_size) ”
  &&  “ ((-1) <= start) ”
  &&  “ (start < 0) ”
  &&  “ (sep = 32) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l 0 start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
.

Definition split_words_entail_wit_2_2 :=
forall (txt_pre: Z) (str_l: (@list Z)) (n: Z) (out: Z) (data: Z) (w: Z) (out_size: Z) (start: Z) (ch: Z) (len: Z) (comma_hit: Z) (space_hit: Z) (sep: Z) (PreH1 : (n = (string_length (str_l)))) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (w = 0)) (PreH5 : (out_size = 0)) (PreH6 : (start = (-1))) (PreH7 : (ch = 0)) (PreH8 : (len = 0)) (PreH9 : (space_hit = 0)) (PreH10 : (comma_hit <> 0)) (PreH11 : ((contains_zb_125 (str_l) (32)) = false)) (PreH12 : ((contains_zb_125 (str_l) (44)) = true)) (PreH13 : (sep = 44)) (PreH14 : (valid_string str_l )) (PreH15 : (all_ascii str_l )) (PreH16 : (valid_split_words_input_125 str_l )) (PreH17 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH18 : (problem_125_pre_z str_l )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string txt_pre str_l )
  **  (PtrArray.undef_full data (n + 1 ) )
|--
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= 0) ”
  &&  “ (0 <= n) ”
  &&  “ (n = (string_length (str_l))) ”
  &&  “ (out <> 0) ”
  &&  “ (data <> 0) ”
  &&  “ (0 <= out_size) ”
  &&  “ (out_size <= 0) ”
  &&  “ (out_size = (Zlength (output_rows))) ”
  &&  “ ((Zlength (output_ptrs)) = out_size) ”
  &&  “ ((-1) <= start) ”
  &&  “ (start < 0) ”
  &&  “ (sep = 44) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l 0 start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= 0) ”
  &&  “ (0 <= n) ”
  &&  “ (n = (string_length (str_l))) ”
  &&  “ (out <> 0) ”
  &&  “ (data <> 0) ”
  &&  “ (0 <= out_size) ”
  &&  “ (out_size <= 0) ”
  &&  “ (out_size = (Zlength (output_rows))) ”
  &&  “ ((Zlength (output_ptrs)) = out_size) ”
  &&  “ ((-1) <= start) ”
  &&  “ (start < 0) ”
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l 0 start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= 0) ”
  &&  “ (0 <= n) ”
  &&  “ (n = (string_length (str_l))) ”
  &&  “ (out <> 0) ”
  &&  “ (data <> 0) ”
  &&  “ (0 <= out_size) ”
  &&  “ (out_size <= 0) ”
  &&  “ (out_size = (Zlength (output_rows))) ”
  &&  “ ((Zlength (output_ptrs)) = out_size) ”
  &&  “ ((-1) <= start) ”
  &&  “ (start < 0) ”
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l 0 start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= 0) ”
  &&  “ (0 <= n) ”
  &&  “ (n = (string_length (str_l))) ”
  &&  “ (out <> 0) ”
  &&  “ (data <> 0) ”
  &&  “ (0 <= out_size) ”
  &&  “ (out_size <= 0) ”
  &&  “ (out_size = (Zlength (output_rows))) ”
  &&  “ ((Zlength (output_ptrs)) = out_size) ”
  &&  “ ((-1) <= start) ”
  &&  “ (start < 0) ”
  &&  “ (sep = 32) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l 0 start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
.

Definition split_words_entail_wit_3_1 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (start >= 0)) (PreH4 : ((Znth i (c_string (str_l)) 0) = sep)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_rows_2)))) (PreH14 : ((Zlength (output_ptrs_2)) = out_size)) (PreH15 : ((-1) <= start)) (PreH16 : (start < i)) (PreH17 : (sep = 44)) (PreH18 : (sep = 44)) (PreH19 : ((contains_zb_125 (str_l) (32)) = false)) (PreH20 : ((contains_zb_125 (str_l) (44)) = true)) (PreH21 : (0 <= ch)) (PreH22 : (ch <= 127)) (PreH23 : (0 <= len)) (PreH24 : (len < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_split_words_input_125 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_125_pre_z str_l )) (PreH30 : (split_scan_state_125 str_l i start sep output_rows_2 )) ,
  (CharArray.undef_full retval ((i - start ) + 1 ) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs_2 output_rows_2 )
|--
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ ((Znth i (c_string (str_l)) 0) = sep) ”
  &&  “ (sep = 44) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (i - start )) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l i start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (i)))) = (i - start )) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full retval 0 (word_payload_125 (str_l) (start) ((start + 0 ))) )
  **  (CharArray.undef_seg retval 0 ((i - start ) + 1 ) ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ ((Znth i (c_string (str_l)) 0) = sep) ”
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (i - start )) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l i start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (i)))) = (i - start )) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full retval 0 (word_payload_125 (str_l) (start) ((start + 0 ))) )
  **  (CharArray.undef_seg retval 0 ((i - start ) + 1 ) ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ ((Znth i (c_string (str_l)) 0) = sep) ”
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (i - start )) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l i start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (i)))) = (i - start )) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full retval 0 (word_payload_125 (str_l) (start) ((start + 0 ))) )
  **  (CharArray.undef_seg retval 0 ((i - start ) + 1 ) ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ ((Znth i (c_string (str_l)) 0) = sep) ”
  &&  “ (sep = 32) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (i - start )) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l i start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (i)))) = (i - start )) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full retval 0 (word_payload_125 (str_l) (start) ((start + 0 ))) )
  **  (CharArray.undef_seg retval 0 ((i - start ) + 1 ) ))
.

Definition split_words_entail_wit_3_2 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (start >= 0)) (PreH4 : ((Znth i (c_string (str_l)) 0) = sep)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_rows_2)))) (PreH14 : ((Zlength (output_ptrs_2)) = out_size)) (PreH15 : ((-1) <= start)) (PreH16 : (start < i)) (PreH17 : (sep = 32)) (PreH18 : (sep = 32)) (PreH19 : ((contains_zb_125 (str_l) (32)) = true)) (PreH20 : (0 <= ch)) (PreH21 : (ch <= 127)) (PreH22 : (0 <= len)) (PreH23 : (len < INT_MAX)) (PreH24 : (valid_string str_l )) (PreH25 : (all_ascii str_l )) (PreH26 : (valid_split_words_input_125 str_l )) (PreH27 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH28 : (problem_125_pre_z str_l )) (PreH29 : (split_scan_state_125 str_l i start sep output_rows_2 )) ,
  (CharArray.undef_full retval ((i - start ) + 1 ) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs_2 output_rows_2 )
|--
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ ((Znth i (c_string (str_l)) 0) = sep) ”
  &&  “ (sep = 44) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (i - start )) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l i start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (i)))) = (i - start )) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full retval 0 (word_payload_125 (str_l) (start) ((start + 0 ))) )
  **  (CharArray.undef_seg retval 0 ((i - start ) + 1 ) ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ ((Znth i (c_string (str_l)) 0) = sep) ”
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (i - start )) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l i start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (i)))) = (i - start )) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full retval 0 (word_payload_125 (str_l) (start) ((start + 0 ))) )
  **  (CharArray.undef_seg retval 0 ((i - start ) + 1 ) ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ ((Znth i (c_string (str_l)) 0) = sep) ”
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (i - start )) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l i start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (i)))) = (i - start )) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full retval 0 (word_payload_125 (str_l) (start) ((start + 0 ))) )
  **  (CharArray.undef_seg retval 0 ((i - start ) + 1 ) ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ ((Znth i (c_string (str_l)) 0) = sep) ”
  &&  “ (sep = 32) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (i - start )) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l i start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (i)))) = (i - start )) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full retval 0 (word_payload_125 (str_l) (start) ((start + 0 ))) )
  **  (CharArray.undef_seg retval 0 ((i - start ) + 1 ) ))
.

Definition split_words_entail_wit_4_1 :=
forall (txt_pre: Z) (str_l: (@list Z)) (k: Z) (sep: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (k < len)) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (w <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : (0 <= start)) (PreH14 : (start < i)) (PreH15 : (len = (i - start ))) (PreH16 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH17 : (ch = sep)) (PreH18 : (sep = 44)) (PreH19 : (sep = 44)) (PreH20 : ((contains_zb_125 (str_l) (32)) = false)) (PreH21 : ((contains_zb_125 (str_l) (44)) = true)) (PreH22 : (0 <= ch)) (PreH23 : (ch <= 127)) (PreH24 : (0 <= k)) (PreH25 : (k <= len)) (PreH26 : (valid_string str_l )) (PreH27 : (all_ascii str_l )) (PreH28 : (valid_split_words_input_125 str_l )) (PreH29 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH30 : (problem_125_pre_z str_l )) (PreH31 : (split_scan_state_125 str_l i start sep output_rows_2 )) (PreH32 : ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i)))) (PreH33 : ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len)) ,
  (CharArray.full w (k + 1 ) (app ((word_payload_125 (str_l) (start) ((start + k )))) ((cons ((Znth (start + k ) (c_string (str_l)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg w (k + 1 ) (len + 1 ) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs_2 output_rows_2 )
|--
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (ch = sep) ”
  &&  “ (sep = 44) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= (k + 1 )) ”
  &&  “ ((k + 1 ) <= len) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l i start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w (k + 1 ) (word_payload_125 (str_l) (start) ((start + (k + 1 ) ))) )
  **  (CharArray.undef_seg w (k + 1 ) (len + 1 ) ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (ch = sep) ”
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= (k + 1 )) ”
  &&  “ ((k + 1 ) <= len) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l i start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w (k + 1 ) (word_payload_125 (str_l) (start) ((start + (k + 1 ) ))) )
  **  (CharArray.undef_seg w (k + 1 ) (len + 1 ) ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (ch = sep) ”
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= (k + 1 )) ”
  &&  “ ((k + 1 ) <= len) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l i start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w (k + 1 ) (word_payload_125 (str_l) (start) ((start + (k + 1 ) ))) )
  **  (CharArray.undef_seg w (k + 1 ) (len + 1 ) ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (ch = sep) ”
  &&  “ (sep = 32) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= (k + 1 )) ”
  &&  “ ((k + 1 ) <= len) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l i start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w (k + 1 ) (word_payload_125 (str_l) (start) ((start + (k + 1 ) ))) )
  **  (CharArray.undef_seg w (k + 1 ) (len + 1 ) ))
.

Definition split_words_entail_wit_4_2 :=
forall (txt_pre: Z) (str_l: (@list Z)) (k: Z) (sep: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (k < len)) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (w <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : (0 <= start)) (PreH14 : (start < i)) (PreH15 : (len = (i - start ))) (PreH16 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH17 : (ch = sep)) (PreH18 : (sep = 32)) (PreH19 : (sep = 32)) (PreH20 : ((contains_zb_125 (str_l) (32)) = true)) (PreH21 : (0 <= ch)) (PreH22 : (ch <= 127)) (PreH23 : (0 <= k)) (PreH24 : (k <= len)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_split_words_input_125 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_125_pre_z str_l )) (PreH30 : (split_scan_state_125 str_l i start sep output_rows_2 )) (PreH31 : ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i)))) (PreH32 : ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len)) ,
  (CharArray.full w (k + 1 ) (app ((word_payload_125 (str_l) (start) ((start + k )))) ((cons ((Znth (start + k ) (c_string (str_l)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg w (k + 1 ) (len + 1 ) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs_2 output_rows_2 )
|--
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (ch = sep) ”
  &&  “ (sep = 44) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= (k + 1 )) ”
  &&  “ ((k + 1 ) <= len) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l i start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w (k + 1 ) (word_payload_125 (str_l) (start) ((start + (k + 1 ) ))) )
  **  (CharArray.undef_seg w (k + 1 ) (len + 1 ) ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (ch = sep) ”
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= (k + 1 )) ”
  &&  “ ((k + 1 ) <= len) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l i start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w (k + 1 ) (word_payload_125 (str_l) (start) ((start + (k + 1 ) ))) )
  **  (CharArray.undef_seg w (k + 1 ) (len + 1 ) ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (ch = sep) ”
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= (k + 1 )) ”
  &&  “ ((k + 1 ) <= len) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l i start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w (k + 1 ) (word_payload_125 (str_l) (start) ((start + (k + 1 ) ))) )
  **  (CharArray.undef_seg w (k + 1 ) (len + 1 ) ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (ch = sep) ”
  &&  “ (sep = 32) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= (k + 1 )) ”
  &&  “ ((k + 1 ) <= len) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l i start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w (k + 1 ) (word_payload_125 (str_l) (start) ((start + (k + 1 ) ))) )
  **  (CharArray.undef_seg w (k + 1 ) (len + 1 ) ))
.

Definition split_words_entail_wit_5_1 :=
forall (txt_pre: Z) (str_l: (@list Z)) (k: Z) (sep: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (k >= len)) (PreH4 : (0 <= i)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (w <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows_2)))) (PreH13 : ((Zlength (output_ptrs_2)) = out_size)) (PreH14 : (0 <= start)) (PreH15 : (start < i)) (PreH16 : (len = (i - start ))) (PreH17 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH18 : (ch = sep)) (PreH19 : (sep = 32)) (PreH20 : (sep = 32)) (PreH21 : ((contains_zb_125 (str_l) (32)) = true)) (PreH22 : (0 <= ch)) (PreH23 : (ch <= 127)) (PreH24 : (0 <= k)) (PreH25 : (k <= len)) (PreH26 : (valid_string str_l )) (PreH27 : (all_ascii str_l )) (PreH28 : (valid_split_words_input_125 str_l )) (PreH29 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH30 : (problem_125_pre_z str_l )) (PreH31 : (split_scan_state_125 str_l i start sep output_rows_2 )) (PreH32 : ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i)))) (PreH33 : ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len)) ,
  (PtrArray.seg data 0 (out_size + 1 ) (app (output_ptrs_2) ((cons (w) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full w (k + 1 ) (app ((word_payload_125 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (split_words_rows_heap_125 output_ptrs_2 output_rows_2 )
|--
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (ch = sep) ”
  &&  “ (sep = 44) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) (-1) sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 (out_size + 1 ) output_ptrs )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (ch = sep) ”
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) (-1) sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 (out_size + 1 ) output_ptrs )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (ch = sep) ”
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) (-1) sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 (out_size + 1 ) output_ptrs )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (ch = sep) ”
  &&  “ (sep = 32) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) (-1) sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 (out_size + 1 ) output_ptrs )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
.

Definition split_words_entail_wit_5_2 :=
forall (txt_pre: Z) (str_l: (@list Z)) (k: Z) (sep: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (k >= len)) (PreH4 : (0 <= i)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (w <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows_2)))) (PreH13 : ((Zlength (output_ptrs_2)) = out_size)) (PreH14 : (0 <= start)) (PreH15 : (start < i)) (PreH16 : (len = (i - start ))) (PreH17 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH18 : (ch = sep)) (PreH19 : (sep = 44)) (PreH20 : (sep = 44)) (PreH21 : ((contains_zb_125 (str_l) (32)) = false)) (PreH22 : ((contains_zb_125 (str_l) (44)) = true)) (PreH23 : (0 <= ch)) (PreH24 : (ch <= 127)) (PreH25 : (0 <= k)) (PreH26 : (k <= len)) (PreH27 : (valid_string str_l )) (PreH28 : (all_ascii str_l )) (PreH29 : (valid_split_words_input_125 str_l )) (PreH30 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH31 : (problem_125_pre_z str_l )) (PreH32 : (split_scan_state_125 str_l i start sep output_rows_2 )) (PreH33 : ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i)))) (PreH34 : ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len)) ,
  (PtrArray.seg data 0 (out_size + 1 ) (app (output_ptrs_2) ((cons (w) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full w (k + 1 ) (app ((word_payload_125 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (split_words_rows_heap_125 output_ptrs_2 output_rows_2 )
|--
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (ch = sep) ”
  &&  “ (sep = 44) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) (-1) sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 (out_size + 1 ) output_ptrs )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (ch = sep) ”
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) (-1) sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 (out_size + 1 ) output_ptrs )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (ch = sep) ”
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) (-1) sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 (out_size + 1 ) output_ptrs )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (ch = sep) ”
  &&  “ (sep = 32) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) (-1) sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 (out_size + 1 ) output_ptrs )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
.

Definition split_words_entail_wit_6_1 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start < 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = sep)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (sep = 32)) (PreH16 : (sep = 32)) (PreH17 : ((contains_zb_125 (str_l) (32)) = true)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_split_words_input_125 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_125_pre_z str_l )) (PreH27 : (split_scan_state_125 str_l i start sep output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs_2 output_rows_2 )
|--
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ ((Znth i (c_string (str_l)) 0) = sep) ”
  &&  “ (sep = 44) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ ((Znth i (c_string (str_l)) 0) = sep) ”
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ ((Znth i (c_string (str_l)) 0) = sep) ”
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ ((Znth i (c_string (str_l)) 0) = sep) ”
  &&  “ (sep = 32) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
.

Definition split_words_entail_wit_6_2 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start < 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = sep)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (sep = 44)) (PreH16 : (sep = 44)) (PreH17 : ((contains_zb_125 (str_l) (32)) = false)) (PreH18 : ((contains_zb_125 (str_l) (44)) = true)) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : (0 <= len)) (PreH22 : (len < INT_MAX)) (PreH23 : (valid_string str_l )) (PreH24 : (all_ascii str_l )) (PreH25 : (valid_split_words_input_125 str_l )) (PreH26 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH27 : (problem_125_pre_z str_l )) (PreH28 : (split_scan_state_125 str_l i start sep output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs_2 output_rows_2 )
|--
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ ((Znth i (c_string (str_l)) 0) = sep) ”
  &&  “ (sep = 44) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ ((Znth i (c_string (str_l)) 0) = sep) ”
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ ((Znth i (c_string (str_l)) 0) = sep) ”
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ ((Znth i (c_string (str_l)) 0) = sep) ”
  &&  “ (sep = 32) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
.

Definition split_words_entail_wit_7_1 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) <> sep)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (sep = 32)) (PreH16 : (sep = 32)) (PreH17 : ((contains_zb_125 (str_l) (32)) = true)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_split_words_input_125 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_125_pre_z str_l )) (PreH27 : (split_scan_state_125 str_l i start sep output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs_2 output_rows_2 )
|--
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ ((Znth i (c_string (str_l)) 0) <> sep) ”
  &&  “ (sep = 44) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ ((Znth i (c_string (str_l)) 0) <> sep) ”
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ ((Znth i (c_string (str_l)) 0) <> sep) ”
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ ((Znth i (c_string (str_l)) 0) <> sep) ”
  &&  “ (sep = 32) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
.

Definition split_words_entail_wit_7_2 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) <> sep)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (sep = 44)) (PreH16 : (sep = 44)) (PreH17 : ((contains_zb_125 (str_l) (32)) = false)) (PreH18 : ((contains_zb_125 (str_l) (44)) = true)) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : (0 <= len)) (PreH22 : (len < INT_MAX)) (PreH23 : (valid_string str_l )) (PreH24 : (all_ascii str_l )) (PreH25 : (valid_split_words_input_125 str_l )) (PreH26 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH27 : (problem_125_pre_z str_l )) (PreH28 : (split_scan_state_125 str_l i start sep output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs_2 output_rows_2 )
|--
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ ((Znth i (c_string (str_l)) 0) <> sep) ”
  &&  “ (sep = 44) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ ((Znth i (c_string (str_l)) 0) <> sep) ”
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ ((Znth i (c_string (str_l)) 0) <> sep) ”
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ ((Znth i (c_string (str_l)) 0) <> sep) ”
  &&  “ (sep = 32) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
.

Definition split_words_entail_wit_7_3 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start < 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) <> sep)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (sep = 32)) (PreH16 : (sep = 32)) (PreH17 : ((contains_zb_125 (str_l) (32)) = true)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_split_words_input_125 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_125_pre_z str_l )) (PreH27 : (split_scan_state_125 str_l i start sep output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs_2 output_rows_2 )
|--
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ ((Znth i (c_string (str_l)) 0) <> sep) ”
  &&  “ (sep = 44) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) i sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ ((Znth i (c_string (str_l)) 0) <> sep) ”
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) i sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ ((Znth i (c_string (str_l)) 0) <> sep) ”
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) i sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ ((Znth i (c_string (str_l)) 0) <> sep) ”
  &&  “ (sep = 32) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) i sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
.

Definition split_words_entail_wit_7_4 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start < 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) <> sep)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (sep = 44)) (PreH16 : (sep = 44)) (PreH17 : ((contains_zb_125 (str_l) (32)) = false)) (PreH18 : ((contains_zb_125 (str_l) (44)) = true)) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : (0 <= len)) (PreH22 : (len < INT_MAX)) (PreH23 : (valid_string str_l )) (PreH24 : (all_ascii str_l )) (PreH25 : (valid_split_words_input_125 str_l )) (PreH26 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH27 : (problem_125_pre_z str_l )) (PreH28 : (split_scan_state_125 str_l i start sep output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs_2 output_rows_2 )
|--
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ ((Znth i (c_string (str_l)) 0) <> sep) ”
  &&  “ (sep = 44) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) i sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ ((Znth i (c_string (str_l)) 0) <> sep) ”
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) i sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ ((Znth i (c_string (str_l)) 0) <> sep) ”
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) i sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ ((Znth i (c_string (str_l)) 0) <> sep) ”
  &&  “ (sep = 32) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) i sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
.

Definition split_words_entail_wit_8_1 :=
forall (txt_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (w: Z) (out_size: Z) (start: Z) (ch: Z) (sep: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (w <> 0)) (PreH7 : (0 <= out_size)) (PreH8 : (out_size <= (i + 1 ))) (PreH9 : (out_size = (Zlength (output_rows_2)))) (PreH10 : ((Zlength (output_ptrs_2)) = out_size)) (PreH11 : (start = (-1))) (PreH12 : (ch = sep)) (PreH13 : (sep = 44)) (PreH14 : (sep = 32)) (PreH15 : ((contains_zb_125 (str_l) (32)) = true)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= len)) (PreH19 : (len < INT_MAX)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_split_words_input_125 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_125_pre_z str_l )) (PreH25 : (split_scan_state_125 str_l (i + 1 ) start sep output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs_2 output_rows_2 )
|--
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
.

Definition split_words_entail_wit_8_2 :=
forall (txt_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (w: Z) (out_size: Z) (start: Z) (ch: Z) (sep: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (w <> 0)) (PreH7 : (0 <= out_size)) (PreH8 : (out_size <= (i + 1 ))) (PreH9 : (out_size = (Zlength (output_rows_2)))) (PreH10 : ((Zlength (output_ptrs_2)) = out_size)) (PreH11 : (start = (-1))) (PreH12 : (ch = sep)) (PreH13 : (sep = 44)) (PreH14 : (sep = 44)) (PreH15 : ((contains_zb_125 (str_l) (32)) = false)) (PreH16 : ((contains_zb_125 (str_l) (44)) = true)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_split_words_input_125 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_125_pre_z str_l )) (PreH26 : (split_scan_state_125 str_l (i + 1 ) start sep output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs_2 output_rows_2 )
|--
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
.

Definition split_words_entail_wit_8_3 :=
forall (txt_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (w: Z) (out_size: Z) (start: Z) (ch: Z) (sep: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (w <> 0)) (PreH7 : (0 <= out_size)) (PreH8 : (out_size <= (i + 1 ))) (PreH9 : (out_size = (Zlength (output_rows_2)))) (PreH10 : ((Zlength (output_ptrs_2)) = out_size)) (PreH11 : (start = (-1))) (PreH12 : (ch = sep)) (PreH13 : (sep = 32)) (PreH14 : (sep = 32)) (PreH15 : ((contains_zb_125 (str_l) (32)) = true)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= len)) (PreH19 : (len < INT_MAX)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_split_words_input_125 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_125_pre_z str_l )) (PreH25 : (split_scan_state_125 str_l (i + 1 ) start sep output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs_2 output_rows_2 )
|--
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
.

Definition split_words_entail_wit_8_4 :=
forall (txt_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (w: Z) (out_size: Z) (start: Z) (ch: Z) (sep: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (w <> 0)) (PreH7 : (0 <= out_size)) (PreH8 : (out_size <= (i + 1 ))) (PreH9 : (out_size = (Zlength (output_rows_2)))) (PreH10 : ((Zlength (output_ptrs_2)) = out_size)) (PreH11 : (start = (-1))) (PreH12 : (ch = sep)) (PreH13 : (sep = 32)) (PreH14 : (sep = 44)) (PreH15 : ((contains_zb_125 (str_l) (32)) = false)) (PreH16 : ((contains_zb_125 (str_l) (44)) = true)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_split_words_input_125 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_125_pre_z str_l )) (PreH26 : (split_scan_state_125 str_l (i + 1 ) start sep output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs_2 output_rows_2 )
|--
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
.

Definition split_words_entail_wit_8_5 :=
forall (txt_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (out_size: Z) (start: Z) (ch: Z) (sep: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= out_size)) (PreH7 : (out_size <= i)) (PreH8 : (out_size = (Zlength (output_rows_2)))) (PreH9 : ((Zlength (output_ptrs_2)) = out_size)) (PreH10 : (start = (-1))) (PreH11 : (ch = sep)) (PreH12 : (sep = 44)) (PreH13 : (sep = 32)) (PreH14 : ((contains_zb_125 (str_l) (32)) = true)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= len)) (PreH18 : (len < INT_MAX)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_split_words_input_125 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_125_pre_z str_l )) (PreH24 : (split_scan_state_125 str_l (i + 1 ) start sep output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs_2 output_rows_2 )
|--
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
.

Definition split_words_entail_wit_8_6 :=
forall (txt_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (out_size: Z) (start: Z) (ch: Z) (sep: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= out_size)) (PreH7 : (out_size <= i)) (PreH8 : (out_size = (Zlength (output_rows_2)))) (PreH9 : ((Zlength (output_ptrs_2)) = out_size)) (PreH10 : (start = (-1))) (PreH11 : (ch = sep)) (PreH12 : (sep = 44)) (PreH13 : (sep = 44)) (PreH14 : ((contains_zb_125 (str_l) (32)) = false)) (PreH15 : ((contains_zb_125 (str_l) (44)) = true)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= len)) (PreH19 : (len < INT_MAX)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_split_words_input_125 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_125_pre_z str_l )) (PreH25 : (split_scan_state_125 str_l (i + 1 ) start sep output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs_2 output_rows_2 )
|--
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
.

Definition split_words_entail_wit_8_7 :=
forall (txt_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (out_size: Z) (start: Z) (ch: Z) (sep: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= out_size)) (PreH7 : (out_size <= i)) (PreH8 : (out_size = (Zlength (output_rows_2)))) (PreH9 : ((Zlength (output_ptrs_2)) = out_size)) (PreH10 : (start = (-1))) (PreH11 : (ch = sep)) (PreH12 : (sep = 32)) (PreH13 : (sep = 32)) (PreH14 : ((contains_zb_125 (str_l) (32)) = true)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= len)) (PreH18 : (len < INT_MAX)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_split_words_input_125 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_125_pre_z str_l )) (PreH24 : (split_scan_state_125 str_l (i + 1 ) start sep output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs_2 output_rows_2 )
|--
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
.

Definition split_words_entail_wit_8_8 :=
forall (txt_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (out_size: Z) (start: Z) (ch: Z) (sep: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= out_size)) (PreH7 : (out_size <= i)) (PreH8 : (out_size = (Zlength (output_rows_2)))) (PreH9 : ((Zlength (output_ptrs_2)) = out_size)) (PreH10 : (start = (-1))) (PreH11 : (ch = sep)) (PreH12 : (sep = 32)) (PreH13 : (sep = 44)) (PreH14 : ((contains_zb_125 (str_l) (32)) = false)) (PreH15 : ((contains_zb_125 (str_l) (44)) = true)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= len)) (PreH19 : (len < INT_MAX)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_split_words_input_125 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_125_pre_z str_l )) (PreH25 : (split_scan_state_125 str_l (i + 1 ) start sep output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs_2 output_rows_2 )
|--
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
.

Definition split_words_entail_wit_8_9 :=
forall (txt_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (out_size: Z) (start: Z) (ch: Z) (sep: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= out_size)) (PreH7 : (out_size <= i)) (PreH8 : (out_size = (Zlength (output_rows_2)))) (PreH9 : ((Zlength (output_ptrs_2)) = out_size)) (PreH10 : (0 <= start)) (PreH11 : (start <= i)) (PreH12 : (ch <> sep)) (PreH13 : (sep = 44)) (PreH14 : (sep = 32)) (PreH15 : ((contains_zb_125 (str_l) (32)) = true)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= len)) (PreH19 : (len < INT_MAX)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_split_words_input_125 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_125_pre_z str_l )) (PreH25 : (split_scan_state_125 str_l (i + 1 ) start sep output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs_2 output_rows_2 )
|--
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
.

Definition split_words_entail_wit_8_10 :=
forall (txt_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (out_size: Z) (start: Z) (ch: Z) (sep: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= out_size)) (PreH7 : (out_size <= i)) (PreH8 : (out_size = (Zlength (output_rows_2)))) (PreH9 : ((Zlength (output_ptrs_2)) = out_size)) (PreH10 : (0 <= start)) (PreH11 : (start <= i)) (PreH12 : (ch <> sep)) (PreH13 : (sep = 44)) (PreH14 : (sep = 44)) (PreH15 : ((contains_zb_125 (str_l) (32)) = false)) (PreH16 : ((contains_zb_125 (str_l) (44)) = true)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_split_words_input_125 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_125_pre_z str_l )) (PreH26 : (split_scan_state_125 str_l (i + 1 ) start sep output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs_2 output_rows_2 )
|--
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
.

Definition split_words_entail_wit_8_11 :=
forall (txt_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (out_size: Z) (start: Z) (ch: Z) (sep: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= out_size)) (PreH7 : (out_size <= i)) (PreH8 : (out_size = (Zlength (output_rows_2)))) (PreH9 : ((Zlength (output_ptrs_2)) = out_size)) (PreH10 : (0 <= start)) (PreH11 : (start <= i)) (PreH12 : (ch <> sep)) (PreH13 : (sep = 32)) (PreH14 : (sep = 32)) (PreH15 : ((contains_zb_125 (str_l) (32)) = true)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= len)) (PreH19 : (len < INT_MAX)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_split_words_input_125 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_125_pre_z str_l )) (PreH25 : (split_scan_state_125 str_l (i + 1 ) start sep output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs_2 output_rows_2 )
|--
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
.

Definition split_words_entail_wit_8_12 :=
forall (txt_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (out_size: Z) (start: Z) (ch: Z) (sep: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= out_size)) (PreH7 : (out_size <= i)) (PreH8 : (out_size = (Zlength (output_rows_2)))) (PreH9 : ((Zlength (output_ptrs_2)) = out_size)) (PreH10 : (0 <= start)) (PreH11 : (start <= i)) (PreH12 : (ch <> sep)) (PreH13 : (sep = 32)) (PreH14 : (sep = 44)) (PreH15 : ((contains_zb_125 (str_l) (32)) = false)) (PreH16 : ((contains_zb_125 (str_l) (44)) = true)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_split_words_input_125 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_125_pre_z str_l )) (PreH26 : (split_scan_state_125 str_l (i + 1 ) start sep output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs_2 output_rows_2 )
|--
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l (i + 1 ) start sep output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
.

Definition split_words_entail_wit_9_1 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (start >= 0)) (PreH4 : (i >= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows_2)))) (PreH13 : ((Zlength (output_ptrs_2)) = out_size)) (PreH14 : ((-1) <= start)) (PreH15 : (start < i)) (PreH16 : (sep = 44)) (PreH17 : (sep = 44)) (PreH18 : ((contains_zb_125 (str_l) (32)) = false)) (PreH19 : ((contains_zb_125 (str_l) (44)) = true)) (PreH20 : (0 <= ch)) (PreH21 : (ch <= 127)) (PreH22 : (0 <= len)) (PreH23 : (len < INT_MAX)) (PreH24 : (valid_string str_l )) (PreH25 : (all_ascii str_l )) (PreH26 : (valid_split_words_input_125 str_l )) (PreH27 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH28 : (problem_125_pre_z str_l )) (PreH29 : (split_scan_state_125 str_l i start sep output_rows_2 )) ,
  (CharArray.undef_full retval ((n - start ) + 1 ) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs_2 output_rows_2 )
|--
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l n start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (n)))) = (n - start )) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full retval 0 (word_payload_125 (str_l) (start) ((start + 0 ))) )
  **  (CharArray.undef_seg retval 0 ((n - start ) + 1 ) ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l n start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (n)))) = (n - start )) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full retval 0 (word_payload_125 (str_l) (start) ((start + 0 ))) )
  **  (CharArray.undef_seg retval 0 ((n - start ) + 1 ) ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l n start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (n)))) = (n - start )) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full retval 0 (word_payload_125 (str_l) (start) ((start + 0 ))) )
  **  (CharArray.undef_seg retval 0 ((n - start ) + 1 ) ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l n start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (n)))) = (n - start )) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full retval 0 (word_payload_125 (str_l) (start) ((start + 0 ))) )
  **  (CharArray.undef_seg retval 0 ((n - start ) + 1 ) ))
.

Definition split_words_entail_wit_9_2 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (start >= 0)) (PreH4 : (i >= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows_2)))) (PreH13 : ((Zlength (output_ptrs_2)) = out_size)) (PreH14 : ((-1) <= start)) (PreH15 : (start < i)) (PreH16 : (sep = 32)) (PreH17 : (sep = 32)) (PreH18 : ((contains_zb_125 (str_l) (32)) = true)) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : (0 <= len)) (PreH22 : (len < INT_MAX)) (PreH23 : (valid_string str_l )) (PreH24 : (all_ascii str_l )) (PreH25 : (valid_split_words_input_125 str_l )) (PreH26 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH27 : (problem_125_pre_z str_l )) (PreH28 : (split_scan_state_125 str_l i start sep output_rows_2 )) ,
  (CharArray.undef_full retval ((n - start ) + 1 ) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs_2 output_rows_2 )
|--
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l n start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (n)))) = (n - start )) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full retval 0 (word_payload_125 (str_l) (start) ((start + 0 ))) )
  **  (CharArray.undef_seg retval 0 ((n - start ) + 1 ) ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l n start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (n)))) = (n - start )) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full retval 0 (word_payload_125 (str_l) (start) ((start + 0 ))) )
  **  (CharArray.undef_seg retval 0 ((n - start ) + 1 ) ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l n start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (n)))) = (n - start )) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full retval 0 (word_payload_125 (str_l) (start) ((start + 0 ))) )
  **  (CharArray.undef_seg retval 0 ((n - start ) + 1 ) ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l n start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (n)))) = (n - start )) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full retval 0 (word_payload_125 (str_l) (start) ((start + 0 ))) )
  **  (CharArray.undef_seg retval 0 ((n - start ) + 1 ) ))
.

Definition split_words_entail_wit_10_1 :=
forall (txt_pre: Z) (str_l: (@list Z)) (sep: Z) (k: Z) (len: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (k < len)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (w <> 0)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= n)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : (0 <= start)) (PreH14 : (start < n)) (PreH15 : (len = (n - start ))) (PreH16 : (0 <= k)) (PreH17 : (k <= len)) (PreH18 : (sep = 44)) (PreH19 : (sep = 44)) (PreH20 : ((contains_zb_125 (str_l) (32)) = false)) (PreH21 : ((contains_zb_125 (str_l) (44)) = true)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_split_words_input_125 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_125_pre_z str_l )) (PreH27 : (split_scan_state_125 str_l n start sep output_rows_2 )) (PreH28 : ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n)))) (PreH29 : ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len)) ,
  (CharArray.full w (k + 1 ) (app ((word_payload_125 (str_l) (start) ((start + k )))) ((cons ((Znth (start + k ) (c_string (str_l)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg w (k + 1 ) (len + 1 ) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs_2 output_rows_2 )
|--
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l n start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w (k + 1 ) (word_payload_125 (str_l) (start) ((start + (k + 1 ) ))) )
  **  (CharArray.undef_seg w (k + 1 ) (len + 1 ) ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l n start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w (k + 1 ) (word_payload_125 (str_l) (start) ((start + (k + 1 ) ))) )
  **  (CharArray.undef_seg w (k + 1 ) (len + 1 ) ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l n start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w (k + 1 ) (word_payload_125 (str_l) (start) ((start + (k + 1 ) ))) )
  **  (CharArray.undef_seg w (k + 1 ) (len + 1 ) ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l n start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w (k + 1 ) (word_payload_125 (str_l) (start) ((start + (k + 1 ) ))) )
  **  (CharArray.undef_seg w (k + 1 ) (len + 1 ) ))
.

Definition split_words_entail_wit_10_2 :=
forall (txt_pre: Z) (str_l: (@list Z)) (sep: Z) (k: Z) (len: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (k < len)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (w <> 0)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= n)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : (0 <= start)) (PreH14 : (start < n)) (PreH15 : (len = (n - start ))) (PreH16 : (0 <= k)) (PreH17 : (k <= len)) (PreH18 : (sep = 32)) (PreH19 : (sep = 32)) (PreH20 : ((contains_zb_125 (str_l) (32)) = true)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_split_words_input_125 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_125_pre_z str_l )) (PreH26 : (split_scan_state_125 str_l n start sep output_rows_2 )) (PreH27 : ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n)))) (PreH28 : ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len)) ,
  (CharArray.full w (k + 1 ) (app ((word_payload_125 (str_l) (start) ((start + k )))) ((cons ((Znth (start + k ) (c_string (str_l)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg w (k + 1 ) (len + 1 ) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs_2 output_rows_2 )
|--
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l n start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w (k + 1 ) (word_payload_125 (str_l) (start) ((start + (k + 1 ) ))) )
  **  (CharArray.undef_seg w (k + 1 ) (len + 1 ) ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l n start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w (k + 1 ) (word_payload_125 (str_l) (start) ((start + (k + 1 ) ))) )
  **  (CharArray.undef_seg w (k + 1 ) (len + 1 ) ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l n start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w (k + 1 ) (word_payload_125 (str_l) (start) ((start + (k + 1 ) ))) )
  **  (CharArray.undef_seg w (k + 1 ) (len + 1 ) ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l n start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w (k + 1 ) (word_payload_125 (str_l) (start) ((start + (k + 1 ) ))) )
  **  (CharArray.undef_seg w (k + 1 ) (len + 1 ) ))
.

Definition split_words_entail_wit_11_1 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start < 0)) (PreH2 : (i >= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows_2)))) (PreH11 : ((Zlength (output_ptrs_2)) = out_size)) (PreH12 : ((-1) <= start)) (PreH13 : (start < i)) (PreH14 : (sep = 32)) (PreH15 : (sep = 32)) (PreH16 : ((contains_zb_125 (str_l) (32)) = true)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_split_words_input_125 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_125_pre_z str_l )) (PreH26 : (split_scan_state_125 str_l i start sep output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs_2 output_rows_2 )
|--
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (output_rows = (split_output_rows_125 (str_l) (sep))) ”
  &&  “ (problem_125_spec_z str_l output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (output_rows = (split_output_rows_125 (str_l) (sep))) ”
  &&  “ (problem_125_spec_z str_l output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (output_rows = (split_output_rows_125 (str_l) (sep))) ”
  &&  “ (problem_125_spec_z str_l output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (output_rows = (split_output_rows_125 (str_l) (sep))) ”
  &&  “ (problem_125_spec_z str_l output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
.

Definition split_words_entail_wit_11_2 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start < 0)) (PreH2 : (i >= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows_2)))) (PreH11 : ((Zlength (output_ptrs_2)) = out_size)) (PreH12 : ((-1) <= start)) (PreH13 : (start < i)) (PreH14 : (sep = 44)) (PreH15 : (sep = 44)) (PreH16 : ((contains_zb_125 (str_l) (32)) = false)) (PreH17 : ((contains_zb_125 (str_l) (44)) = true)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_split_words_input_125 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_125_pre_z str_l )) (PreH27 : (split_scan_state_125 str_l i start sep output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs_2 output_rows_2 )
|--
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (output_rows = (split_output_rows_125 (str_l) (sep))) ”
  &&  “ (problem_125_spec_z str_l output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (output_rows = (split_output_rows_125 (str_l) (sep))) ”
  &&  “ (problem_125_spec_z str_l output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (output_rows = (split_output_rows_125 (str_l) (sep))) ”
  &&  “ (problem_125_spec_z str_l output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (output_rows = (split_output_rows_125 (str_l) (sep))) ”
  &&  “ (problem_125_spec_z str_l output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
.

Definition split_words_entail_wit_11_3 :=
forall (txt_pre: Z) (str_l: (@list Z)) (sep: Z) (k: Z) (len: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (k >= len)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= n)) (PreH12 : (out_size = (Zlength (output_rows_2)))) (PreH13 : ((Zlength (output_ptrs_2)) = out_size)) (PreH14 : (0 <= start)) (PreH15 : (start < n)) (PreH16 : (len = (n - start ))) (PreH17 : (0 <= k)) (PreH18 : (k <= len)) (PreH19 : (sep = 32)) (PreH20 : (sep = 32)) (PreH21 : ((contains_zb_125 (str_l) (32)) = true)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_split_words_input_125 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_125_pre_z str_l )) (PreH27 : (split_scan_state_125 str_l n start sep output_rows_2 )) (PreH28 : ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n)))) (PreH29 : ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len)) ,
  (PtrArray.seg data 0 (out_size + 1 ) (app (output_ptrs_2) ((cons (w) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full w (k + 1 ) (app ((word_payload_125 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (split_words_rows_heap_125 output_ptrs_2 output_rows_2 )
|--
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (output_rows = (split_output_rows_125 (str_l) (sep))) ”
  &&  “ (problem_125_spec_z str_l output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 (out_size + 1 ) output_ptrs )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (output_rows = (split_output_rows_125 (str_l) (sep))) ”
  &&  “ (problem_125_spec_z str_l output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 (out_size + 1 ) output_ptrs )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (output_rows = (split_output_rows_125 (str_l) (sep))) ”
  &&  “ (problem_125_spec_z str_l output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 (out_size + 1 ) output_ptrs )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (output_rows = (split_output_rows_125 (str_l) (sep))) ”
  &&  “ (problem_125_spec_z str_l output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 (out_size + 1 ) output_ptrs )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
.

Definition split_words_entail_wit_11_4 :=
forall (txt_pre: Z) (str_l: (@list Z)) (sep: Z) (k: Z) (len: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (k >= len)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= n)) (PreH12 : (out_size = (Zlength (output_rows_2)))) (PreH13 : ((Zlength (output_ptrs_2)) = out_size)) (PreH14 : (0 <= start)) (PreH15 : (start < n)) (PreH16 : (len = (n - start ))) (PreH17 : (0 <= k)) (PreH18 : (k <= len)) (PreH19 : (sep = 44)) (PreH20 : (sep = 44)) (PreH21 : ((contains_zb_125 (str_l) (32)) = false)) (PreH22 : ((contains_zb_125 (str_l) (44)) = true)) (PreH23 : (valid_string str_l )) (PreH24 : (all_ascii str_l )) (PreH25 : (valid_split_words_input_125 str_l )) (PreH26 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH27 : (problem_125_pre_z str_l )) (PreH28 : (split_scan_state_125 str_l n start sep output_rows_2 )) (PreH29 : ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n)))) (PreH30 : ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len)) ,
  (PtrArray.seg data 0 (out_size + 1 ) (app (output_ptrs_2) ((cons (w) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full w (k + 1 ) (app ((word_payload_125 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (split_words_rows_heap_125 output_ptrs_2 output_rows_2 )
|--
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (output_rows = (split_output_rows_125 (str_l) (sep))) ”
  &&  “ (problem_125_spec_z str_l output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 (out_size + 1 ) output_ptrs )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (output_rows = (split_output_rows_125 (str_l) (sep))) ”
  &&  “ (problem_125_spec_z str_l output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 (out_size + 1 ) output_ptrs )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (output_rows = (split_output_rows_125 (str_l) (sep))) ”
  &&  “ (problem_125_spec_z str_l output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 (out_size + 1 ) output_ptrs )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
  ||
  (EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (output_rows = (split_output_rows_125 (str_l) (sep))) ”
  &&  “ (problem_125_spec_z str_l output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 (out_size + 1 ) output_ptrs )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows ))
.

Definition split_words_entail_wit_12 :=
(
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_2 = 0)) (PreH3 : (retval_5 <> 0)) (PreH4 : (retval_4 <> 0)) (PreH5 : (strchr_result str_l 44 retval_3 txt_pre )) (PreH6 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH7 : (retval = (string_length (str_l)))) (PreH8 : (0 <= ((string_length (str_l)) + 1 ))) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (valid_split_words_input_125 str_l )) (PreH12 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH13 : (problem_125_pre_z str_l )) ,
  (PtrArray.undef_full retval_5 (retval + 1 ) )
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_5)
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
|--
  “ (0 <= 0) ”
  &&  “ (0 <= retval) ”
  &&  “ (retval = (string_length (str_l))) ”
  &&  “ (retval_4 <> 0) ”
  &&  “ (retval_5 <> 0) ”
  &&  “ (0 = (odd_lower_prefix_125 (str_l) (0))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 < INT_MAX) ”
  &&  “ (retval_2 = 0) ”
  &&  “ (retval_3 = 0) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = false) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  ((&((retval_4)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_5)
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string txt_pre str_l )
  **  (PtrArray.undef_full retval_5 (retval + 1 ) )
) \/
(
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_2 = 0)) (PreH3 : (retval_5 <> 0)) (PreH4 : (retval_4 <> 0)) (PreH5 : (strchr_result str_l 44 retval_3 txt_pre )) (PreH6 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH7 : (retval = (string_length (str_l)))) (PreH8 : (0 <= ((string_length (str_l)) + 1 ))) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (valid_split_words_input_125 str_l )) (PreH12 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH13 : (problem_125_pre_z str_l )) ,
  (PtrArray.undef_full retval_5 (retval + 1 ) )
|--
  “ ((contains_zb_125 (str_l) (44)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ (0 = (odd_lower_prefix_125 (str_l) (0))) ”
  &&  “ (0 <= retval) ”
  &&  (PtrArray.undef_full retval_5 (retval + 1 ) )
).

Definition split_words_entail_wit_12_split_goal_1 :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_2 = 0)) (PreH3 : (retval_5 <> 0)) (PreH4 : (retval_4 <> 0)) (PreH5 : (strchr_result str_l 44 retval_3 txt_pre )) (PreH6 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH7 : (retval = (string_length (str_l)))) (PreH8 : (0 <= ((string_length (str_l)) + 1 ))) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (valid_split_words_input_125 str_l )) (PreH12 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH13 : (problem_125_pre_z str_l )) ,
  (PtrArray.undef_full retval_5 (retval + 1 ) )
|--
  “ ((contains_zb_125 (str_l) (44)) = false) ”
.

Definition split_words_entail_wit_12_split_goal_2 :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_2 = 0)) (PreH3 : (retval_5 <> 0)) (PreH4 : (retval_4 <> 0)) (PreH5 : (strchr_result str_l 44 retval_3 txt_pre )) (PreH6 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH7 : (retval = (string_length (str_l)))) (PreH8 : (0 <= ((string_length (str_l)) + 1 ))) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (valid_split_words_input_125 str_l )) (PreH12 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH13 : (problem_125_pre_z str_l )) ,
  (PtrArray.undef_full retval_5 (retval + 1 ) )
|--
  “ ((contains_zb_125 (str_l) (32)) = false) ”
.

Definition split_words_entail_wit_12_split_goal_3 :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_2 = 0)) (PreH3 : (retval_5 <> 0)) (PreH4 : (retval_4 <> 0)) (PreH5 : (strchr_result str_l 44 retval_3 txt_pre )) (PreH6 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH7 : (retval = (string_length (str_l)))) (PreH8 : (0 <= ((string_length (str_l)) + 1 ))) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (valid_split_words_input_125 str_l )) (PreH12 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH13 : (problem_125_pre_z str_l )) ,
  (PtrArray.undef_full retval_5 (retval + 1 ) )
|--
  “ (0 = (odd_lower_prefix_125 (str_l) (0))) ”
.

Definition split_words_entail_wit_12_split_goal_4 :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_2 = 0)) (PreH3 : (retval_5 <> 0)) (PreH4 : (retval_4 <> 0)) (PreH5 : (strchr_result str_l 44 retval_3 txt_pre )) (PreH6 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH7 : (retval = (string_length (str_l)))) (PreH8 : (0 <= ((string_length (str_l)) + 1 ))) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (valid_split_words_input_125 str_l )) (PreH12 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH13 : (problem_125_pre_z str_l )) ,
  (PtrArray.undef_full retval_5 (retval + 1 ) )
|--
  “ (0 <= retval) ”
.

Definition split_words_entail_wit_12_split_goal_spatial :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_2 = 0)) (PreH3 : (retval_5 <> 0)) (PreH4 : (retval_4 <> 0)) (PreH5 : (strchr_result str_l 44 retval_3 txt_pre )) (PreH6 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH7 : (retval = (string_length (str_l)))) (PreH8 : (0 <= ((string_length (str_l)) + 1 ))) (PreH9 : (valid_string str_l )) (PreH10 : (all_ascii str_l )) (PreH11 : (valid_split_words_input_125 str_l )) (PreH12 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH13 : (problem_125_pre_z str_l )) ,
  (PtrArray.undef_full retval_5 (retval + 1 ) )
|--
  (PtrArray.undef_full retval_5 (retval + 1 ) )
.

Definition split_words_entail_wit_13_1 :=
(
forall (txt_pre: Z) (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (((Znth i (c_string (str_l)) 0) % ( 2 ) ) = 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) <= 122)) (PreH3 : ((Znth i (c_string (str_l)) 0) >= 97)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (0 <= len)) (PreH14 : (len < INT_MAX)) (PreH15 : (space_hit = 0)) (PreH16 : (comma_hit = 0)) (PreH17 : ((contains_zb_125 (str_l) (32)) = false)) (PreH18 : ((contains_zb_125 (str_l) (44)) = false)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_split_words_input_125 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_125_pre_z str_l )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string txt_pre str_l )
  **  (PtrArray.undef_full data (n + 1 ) )
|--
  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n) ”
  &&  “ (n = (string_length (str_l))) ”
  &&  “ (out <> 0) ”
  &&  “ (data <> 0) ”
  &&  “ ((out_size + 1 ) = (odd_lower_prefix_125 (str_l) ((i + 1 )))) ”
  &&  “ (0 <= (out_size + 1 )) ”
  &&  “ ((out_size + 1 ) <= (i + 1 )) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (space_hit = 0) ”
  &&  “ (comma_hit = 0) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = false) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string txt_pre str_l )
  **  (PtrArray.undef_full data (n + 1 ) )
) \/
(
forall (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (((Znth i (c_string (str_l)) 0) % ( 2 ) ) = 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) <= 122)) (PreH4 : ((Znth i (c_string (str_l)) 0) >= 97)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (0 <= len)) (PreH15 : (len < INT_MAX)) (PreH16 : (space_hit = 0)) (PreH17 : (comma_hit = 0)) (PreH18 : ((contains_zb_125 (str_l) (32)) = false)) (PreH19 : ((contains_zb_125 (str_l) (44)) = false)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_split_words_input_125 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_125_pre_z str_l )) ,
  (PtrArray.undef_full data (n + 1 ) )
|--
  “ ((out_size + 1 ) = (odd_lower_prefix_125 (str_l) ((i + 1 )))) ”
  &&  (PtrArray.undef_full data (n + 1 ) )
).

Definition split_words_entail_wit_13_1_split_goal_1 :=
forall (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (((Znth i (c_string (str_l)) 0) % ( 2 ) ) = 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) <= 122)) (PreH4 : ((Znth i (c_string (str_l)) 0) >= 97)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (0 <= len)) (PreH15 : (len < INT_MAX)) (PreH16 : (space_hit = 0)) (PreH17 : (comma_hit = 0)) (PreH18 : ((contains_zb_125 (str_l) (32)) = false)) (PreH19 : ((contains_zb_125 (str_l) (44)) = false)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_split_words_input_125 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_125_pre_z str_l )) ,
  (PtrArray.undef_full data (n + 1 ) )
|--
  “ ((out_size + 1 ) = (odd_lower_prefix_125 (str_l) ((i + 1 )))) ”
.

Definition split_words_entail_wit_13_1_split_goal_spatial :=
forall (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (((Znth i (c_string (str_l)) 0) % ( 2 ) ) = 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) <= 122)) (PreH4 : ((Znth i (c_string (str_l)) 0) >= 97)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (0 <= len)) (PreH15 : (len < INT_MAX)) (PreH16 : (space_hit = 0)) (PreH17 : (comma_hit = 0)) (PreH18 : ((contains_zb_125 (str_l) (32)) = false)) (PreH19 : ((contains_zb_125 (str_l) (44)) = false)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_split_words_input_125 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_125_pre_z str_l )) ,
  (PtrArray.undef_full data (n + 1 ) )
|--
  (PtrArray.undef_full data (n + 1 ) )
.

Definition split_words_entail_wit_13_2 :=
(
forall (txt_pre: Z) (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) > 122)) (PreH2 : ((Znth i (c_string (str_l)) 0) >= 97)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (0 <= len)) (PreH13 : (len < INT_MAX)) (PreH14 : (space_hit = 0)) (PreH15 : (comma_hit = 0)) (PreH16 : ((contains_zb_125 (str_l) (32)) = false)) (PreH17 : ((contains_zb_125 (str_l) (44)) = false)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (valid_split_words_input_125 str_l )) (PreH21 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH22 : (problem_125_pre_z str_l )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string txt_pre str_l )
  **  (PtrArray.undef_full data (n + 1 ) )
|--
  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n) ”
  &&  “ (n = (string_length (str_l))) ”
  &&  “ (out <> 0) ”
  &&  “ (data <> 0) ”
  &&  “ (out_size = (odd_lower_prefix_125 (str_l) ((i + 1 )))) ”
  &&  “ (0 <= out_size) ”
  &&  “ (out_size <= (i + 1 )) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (space_hit = 0) ”
  &&  “ (comma_hit = 0) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = false) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string txt_pre str_l )
  **  (PtrArray.undef_full data (n + 1 ) )
) \/
(
forall (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth i (c_string (str_l)) 0) > 122)) (PreH3 : ((Znth i (c_string (str_l)) 0) >= 97)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (0 <= len)) (PreH14 : (len < INT_MAX)) (PreH15 : (space_hit = 0)) (PreH16 : (comma_hit = 0)) (PreH17 : ((contains_zb_125 (str_l) (32)) = false)) (PreH18 : ((contains_zb_125 (str_l) (44)) = false)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_split_words_input_125 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_125_pre_z str_l )) ,
  (PtrArray.undef_full data (n + 1 ) )
|--
  “ (out_size = (odd_lower_prefix_125 (str_l) ((i + 1 )))) ”
  &&  (PtrArray.undef_full data (n + 1 ) )
).

Definition split_words_entail_wit_13_2_split_goal_1 :=
forall (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth i (c_string (str_l)) 0) > 122)) (PreH3 : ((Znth i (c_string (str_l)) 0) >= 97)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (0 <= len)) (PreH14 : (len < INT_MAX)) (PreH15 : (space_hit = 0)) (PreH16 : (comma_hit = 0)) (PreH17 : ((contains_zb_125 (str_l) (32)) = false)) (PreH18 : ((contains_zb_125 (str_l) (44)) = false)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_split_words_input_125 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_125_pre_z str_l )) ,
  (PtrArray.undef_full data (n + 1 ) )
|--
  “ (out_size = (odd_lower_prefix_125 (str_l) ((i + 1 )))) ”
.

Definition split_words_entail_wit_13_2_split_goal_spatial :=
forall (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth i (c_string (str_l)) 0) > 122)) (PreH3 : ((Znth i (c_string (str_l)) 0) >= 97)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (0 <= len)) (PreH14 : (len < INT_MAX)) (PreH15 : (space_hit = 0)) (PreH16 : (comma_hit = 0)) (PreH17 : ((contains_zb_125 (str_l) (32)) = false)) (PreH18 : ((contains_zb_125 (str_l) (44)) = false)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_split_words_input_125 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_125_pre_z str_l )) ,
  (PtrArray.undef_full data (n + 1 ) )
|--
  (PtrArray.undef_full data (n + 1 ) )
.

Definition split_words_entail_wit_13_3 :=
(
forall (txt_pre: Z) (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) < 97)) (PreH2 : (i < n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (0 <= len)) (PreH12 : (len < INT_MAX)) (PreH13 : (space_hit = 0)) (PreH14 : (comma_hit = 0)) (PreH15 : ((contains_zb_125 (str_l) (32)) = false)) (PreH16 : ((contains_zb_125 (str_l) (44)) = false)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (valid_split_words_input_125 str_l )) (PreH20 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH21 : (problem_125_pre_z str_l )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string txt_pre str_l )
  **  (PtrArray.undef_full data (n + 1 ) )
|--
  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n) ”
  &&  “ (n = (string_length (str_l))) ”
  &&  “ (out <> 0) ”
  &&  “ (data <> 0) ”
  &&  “ (out_size = (odd_lower_prefix_125 (str_l) ((i + 1 )))) ”
  &&  “ (0 <= out_size) ”
  &&  “ (out_size <= (i + 1 )) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (space_hit = 0) ”
  &&  “ (comma_hit = 0) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = false) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string txt_pre str_l )
  **  (PtrArray.undef_full data (n + 1 ) )
) \/
(
forall (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth i (c_string (str_l)) 0) < 97)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (0 <= len)) (PreH13 : (len < INT_MAX)) (PreH14 : (space_hit = 0)) (PreH15 : (comma_hit = 0)) (PreH16 : ((contains_zb_125 (str_l) (32)) = false)) (PreH17 : ((contains_zb_125 (str_l) (44)) = false)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (valid_split_words_input_125 str_l )) (PreH21 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH22 : (problem_125_pre_z str_l )) ,
  (PtrArray.undef_full data (n + 1 ) )
|--
  “ (out_size = (odd_lower_prefix_125 (str_l) ((i + 1 )))) ”
  &&  (PtrArray.undef_full data (n + 1 ) )
).

Definition split_words_entail_wit_13_3_split_goal_1 :=
forall (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth i (c_string (str_l)) 0) < 97)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (0 <= len)) (PreH13 : (len < INT_MAX)) (PreH14 : (space_hit = 0)) (PreH15 : (comma_hit = 0)) (PreH16 : ((contains_zb_125 (str_l) (32)) = false)) (PreH17 : ((contains_zb_125 (str_l) (44)) = false)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (valid_split_words_input_125 str_l )) (PreH21 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH22 : (problem_125_pre_z str_l )) ,
  (PtrArray.undef_full data (n + 1 ) )
|--
  “ (out_size = (odd_lower_prefix_125 (str_l) ((i + 1 )))) ”
.

Definition split_words_entail_wit_13_3_split_goal_spatial :=
forall (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth i (c_string (str_l)) 0) < 97)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (0 <= len)) (PreH13 : (len < INT_MAX)) (PreH14 : (space_hit = 0)) (PreH15 : (comma_hit = 0)) (PreH16 : ((contains_zb_125 (str_l) (32)) = false)) (PreH17 : ((contains_zb_125 (str_l) (44)) = false)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (valid_split_words_input_125 str_l )) (PreH21 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH22 : (problem_125_pre_z str_l )) ,
  (PtrArray.undef_full data (n + 1 ) )
|--
  (PtrArray.undef_full data (n + 1 ) )
.

Definition split_words_entail_wit_13_4 :=
(
forall (txt_pre: Z) (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (((Znth i (c_string (str_l)) 0) % ( 2 ) ) <> 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) <= 122)) (PreH3 : ((Znth i (c_string (str_l)) 0) >= 97)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (0 <= len)) (PreH14 : (len < INT_MAX)) (PreH15 : (space_hit = 0)) (PreH16 : (comma_hit = 0)) (PreH17 : ((contains_zb_125 (str_l) (32)) = false)) (PreH18 : ((contains_zb_125 (str_l) (44)) = false)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_split_words_input_125 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_125_pre_z str_l )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string txt_pre str_l )
  **  (PtrArray.undef_full data (n + 1 ) )
|--
  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n) ”
  &&  “ (n = (string_length (str_l))) ”
  &&  “ (out <> 0) ”
  &&  “ (data <> 0) ”
  &&  “ (out_size = (odd_lower_prefix_125 (str_l) ((i + 1 )))) ”
  &&  “ (0 <= out_size) ”
  &&  “ (out_size <= (i + 1 )) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (space_hit = 0) ”
  &&  “ (comma_hit = 0) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = false) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string txt_pre str_l )
  **  (PtrArray.undef_full data (n + 1 ) )
) \/
(
forall (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (((Znth i (c_string (str_l)) 0) % ( 2 ) ) <> 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) <= 122)) (PreH4 : ((Znth i (c_string (str_l)) 0) >= 97)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (0 <= len)) (PreH15 : (len < INT_MAX)) (PreH16 : (space_hit = 0)) (PreH17 : (comma_hit = 0)) (PreH18 : ((contains_zb_125 (str_l) (32)) = false)) (PreH19 : ((contains_zb_125 (str_l) (44)) = false)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_split_words_input_125 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_125_pre_z str_l )) ,
  (PtrArray.undef_full data (n + 1 ) )
|--
  “ (out_size = (odd_lower_prefix_125 (str_l) ((i + 1 )))) ”
  &&  (PtrArray.undef_full data (n + 1 ) )
).

Definition split_words_entail_wit_13_4_split_goal_1 :=
forall (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (((Znth i (c_string (str_l)) 0) % ( 2 ) ) <> 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) <= 122)) (PreH4 : ((Znth i (c_string (str_l)) 0) >= 97)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (0 <= len)) (PreH15 : (len < INT_MAX)) (PreH16 : (space_hit = 0)) (PreH17 : (comma_hit = 0)) (PreH18 : ((contains_zb_125 (str_l) (32)) = false)) (PreH19 : ((contains_zb_125 (str_l) (44)) = false)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_split_words_input_125 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_125_pre_z str_l )) ,
  (PtrArray.undef_full data (n + 1 ) )
|--
  “ (out_size = (odd_lower_prefix_125 (str_l) ((i + 1 )))) ”
.

Definition split_words_entail_wit_13_4_split_goal_spatial :=
forall (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (((Znth i (c_string (str_l)) 0) % ( 2 ) ) <> 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) <= 122)) (PreH4 : ((Znth i (c_string (str_l)) 0) >= 97)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (0 <= len)) (PreH15 : (len < INT_MAX)) (PreH16 : (space_hit = 0)) (PreH17 : (comma_hit = 0)) (PreH18 : ((contains_zb_125 (str_l) (32)) = false)) (PreH19 : ((contains_zb_125 (str_l) (44)) = false)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_split_words_input_125 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_125_pre_z str_l )) ,
  (PtrArray.undef_full data (n + 1 ) )
|--
  (PtrArray.undef_full data (n + 1 ) )
.

Definition split_words_entail_wit_14 :=
(
forall (txt_pre: Z) (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (retval_2: Z) (out_l: (@list Z)) (PreH1 : (0 <= (retval + 1 ))) (PreH2 : ((Zlength (out_l)) = retval)) (PreH3 : (retval_2 <> 0)) (PreH4 : (1 <= retval)) (PreH5 : (retval < INT_MAX)) (PreH6 : (0 <= ((string_length (str_l)) + 1 ))) (PreH7 : (i >= n)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (n = (string_length (str_l)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH14 : (0 <= out_size)) (PreH15 : (out_size <= i)) (PreH16 : (0 <= len)) (PreH17 : (len < INT_MAX)) (PreH18 : (space_hit = 0)) (PreH19 : (comma_hit = 0)) (PreH20 : ((contains_zb_125 (str_l) (32)) = false)) (PreH21 : ((contains_zb_125 (str_l) (44)) = false)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_split_words_input_125 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_125_pre_z str_l )) ,
  (((data + (0 * sizeof(PTR) ) )) # Ptr  |-> retval_2)
  **  (PtrArray.undef_missing_i data 0 0 (n + 1 ) )
  **  (CharArray.full retval_2 (retval + 1 ) (c_string (out_l)) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 1)
|--
  EX (output_ptrs: (@list Z))  (digit_l: (@list Z)) ,
  “ (n = (string_length (str_l))) ”
  &&  “ (out <> 0) ”
  &&  “ (data <> 0) ”
  &&  “ (retval_2 <> 0) ”
  &&  “ ((Zlength (digit_l)) = retval) ”
  &&  “ (out_size = (odd_lower_count_125 (str_l))) ”
  &&  “ (space_hit = 0) ”
  &&  “ (comma_hit = 0) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = false) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (output_ptrs = (cons (retval_2) ((@nil Z)))) ”
  &&  “ (problem_125_spec_z str_l (cons ((c_string (digit_l))) ((@nil (@list Z)))) ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 1)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 1 output_ptrs )
  **  (PtrArray.undef_seg data 1 (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs (cons ((c_string (digit_l))) ((@nil (@list Z)))) )
) \/
(
forall (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (retval_2: Z) (out_l: (@list Z)) (PreH1 : (0 <= (retval + 1 ))) (PreH2 : ((Zlength (out_l)) = retval)) (PreH3 : (retval_2 <> 0)) (PreH4 : (1 <= retval)) (PreH5 : (retval < INT_MAX)) (PreH6 : (0 <= ((string_length (str_l)) + 1 ))) (PreH7 : (i >= n)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (n = (string_length (str_l)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH14 : (0 <= out_size)) (PreH15 : (out_size <= i)) (PreH16 : (0 <= len)) (PreH17 : (len < INT_MAX)) (PreH18 : (space_hit = 0)) (PreH19 : (comma_hit = 0)) (PreH20 : ((contains_zb_125 (str_l) (32)) = false)) (PreH21 : ((contains_zb_125 (str_l) (44)) = false)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_split_words_input_125 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_125_pre_z str_l )) ,
  (((data + (0 * sizeof(PTR) ) )) # Ptr  |-> retval_2)
  **  (PtrArray.undef_missing_i data 0 0 (n + 1 ) )
  **  (CharArray.full retval_2 (retval + 1 ) (c_string (out_l)) )
|--
  EX (digit_l: (@list Z)) ,
  “ (n = (string_length (str_l))) ”
  &&  “ (out <> 0) ”
  &&  “ (data <> 0) ”
  &&  “ (retval_2 <> 0) ”
  &&  “ ((Zlength (digit_l)) = retval) ”
  &&  “ (out_size = (odd_lower_count_125 (str_l))) ”
  &&  “ (space_hit = 0) ”
  &&  “ (comma_hit = 0) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = false) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (problem_125_spec_z str_l (cons ((c_string (digit_l))) ((@nil (@list Z)))) ) ”
  &&  (PtrArray.seg data 0 1 (cons (retval_2) ((@nil Z))) )
  **  (PtrArray.undef_seg data 1 (n + 1 ) )
  **  (split_words_rows_heap_125 (cons (retval_2) ((@nil Z))) (cons ((c_string (digit_l))) ((@nil (@list Z)))) )
).

Definition split_words_return_wit_1 :=
(
forall (txt_pre: Z) (str_l: (@list Z)) (output_ptrs_2: (@list Z)) (digit_l: (@list Z)) (n: Z) (out: Z) (data_2: Z) (w: Z) (len: Z) (out_size: Z) (space_hit: Z) (comma_hit: Z) (PreH1 : (n = (string_length (str_l)))) (PreH2 : (out <> 0)) (PreH3 : (data_2 <> 0)) (PreH4 : (w <> 0)) (PreH5 : ((Zlength (digit_l)) = len)) (PreH6 : (out_size = (odd_lower_count_125 (str_l)))) (PreH7 : (space_hit = 0)) (PreH8 : (comma_hit = 0)) (PreH9 : ((contains_zb_125 (str_l) (32)) = false)) (PreH10 : ((contains_zb_125 (str_l) (44)) = false)) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (valid_split_words_input_125 str_l )) (PreH14 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH15 : (problem_125_pre_z str_l )) (PreH16 : (output_ptrs_2 = (cons (w) ((@nil Z))))) (PreH17 : (problem_125_spec_z str_l (cons ((c_string (digit_l))) ((@nil (@list Z)))) )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 1)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data_2 0 1 output_ptrs_2 )
  **  (PtrArray.undef_seg data_2 1 (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs_2 (cons ((c_string (digit_l))) ((@nil (@list Z)))) )
|--
  EX (output_rows: (@list (@list Z)))  (output_ptrs: (@list Z))  (data: Z) ,
  “ (out <> 0) ”
  &&  “ (data <> 0) ”
  &&  “ ((Zlength (output_ptrs)) = (Zlength (output_rows))) ”
  &&  “ ((Zlength (output_rows)) <= ((string_length (str_l)) + 1 )) ”
  &&  “ (problem_125_spec_z str_l output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows)))
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
) \/
(
forall (str_l: (@list Z)) (output_ptrs_2: (@list Z)) (digit_l: (@list Z)) (n: Z) (out: Z) (data_2: Z) (w: Z) (len: Z) (out_size: Z) (space_hit: Z) (comma_hit: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (n = (string_length (str_l)))) (PreH3 : (out <> 0)) (PreH4 : (data_2 <> 0)) (PreH5 : (w <> 0)) (PreH6 : ((Zlength (digit_l)) = len)) (PreH7 : (out_size = (odd_lower_count_125 (str_l)))) (PreH8 : (space_hit = 0)) (PreH9 : (comma_hit = 0)) (PreH10 : ((contains_zb_125 (str_l) (32)) = false)) (PreH11 : ((contains_zb_125 (str_l) (44)) = false)) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (valid_split_words_input_125 str_l )) (PreH15 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH16 : (problem_125_pre_z str_l )) (PreH17 : (output_ptrs_2 = (cons (w) ((@nil Z))))) (PreH18 : (problem_125_spec_z str_l (cons ((c_string (digit_l))) ((@nil (@list Z)))) )) ,
  (PtrArray.seg data_2 0 1 output_ptrs_2 )
  **  (PtrArray.undef_seg data_2 1 (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs_2 (cons ((c_string (digit_l))) ((@nil (@list Z)))) )
|--
  EX (output_rows: (@list (@list Z)))  (output_ptrs: (@list Z)) ,
  “ (1 = (Zlength (output_rows))) ”
  &&  “ (out <> 0) ”
  &&  “ (data_2 <> 0) ”
  &&  “ ((Zlength (output_ptrs)) = (Zlength (output_rows))) ”
  &&  “ ((Zlength (output_rows)) <= ((string_length (str_l)) + 1 )) ”
  &&  “ (problem_125_spec_z str_l output_rows ) ”
  &&  (PtrArray.seg data_2 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data_2 (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
).

Definition split_words_return_wit_2 :=
forall (txt_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (n: Z) (out: Z) (data_2: Z) (ch: Z) (len: Z) (out_size: Z) (start: Z) (sep: Z) (PreH1 : (n = (string_length (str_l)))) (PreH2 : (out <> 0)) (PreH3 : (data_2 <> 0)) (PreH4 : (0 <= ch)) (PreH5 : (ch <= 127)) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (out_size = (Zlength (output_rows_2)))) (PreH9 : ((Zlength (output_ptrs_2)) = out_size)) (PreH10 : (start = (-1))) (PreH11 : (sep = 32)) (PreH12 : (sep = 44)) (PreH13 : ((contains_zb_125 (str_l) (32)) = false)) (PreH14 : ((contains_zb_125 (str_l) (44)) = true)) (PreH15 : (valid_string str_l )) (PreH16 : (all_ascii str_l )) (PreH17 : (valid_split_words_input_125 str_l )) (PreH18 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH19 : (problem_125_pre_z str_l )) (PreH20 : (output_rows_2 = (split_output_rows_125 (str_l) (sep)))) (PreH21 : (problem_125_spec_z str_l output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data_2 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data_2 out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs_2 output_rows_2 )
|--
  EX (output_rows: (@list (@list Z)))  (output_ptrs: (@list Z))  (data: Z) ,
  “ (out <> 0) ”
  &&  “ (data <> 0) ”
  &&  “ ((Zlength (output_ptrs)) = (Zlength (output_rows))) ”
  &&  “ ((Zlength (output_rows)) <= ((string_length (str_l)) + 1 )) ”
  &&  “ (problem_125_spec_z str_l output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows)))
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
.

Definition split_words_return_wit_3 :=
(
forall (txt_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (n: Z) (out: Z) (data_2: Z) (ch: Z) (len: Z) (out_size: Z) (start: Z) (sep: Z) (PreH1 : (n = (string_length (str_l)))) (PreH2 : (out <> 0)) (PreH3 : (data_2 <> 0)) (PreH4 : (0 <= ch)) (PreH5 : (ch <= 127)) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (out_size = (Zlength (output_rows_2)))) (PreH9 : ((Zlength (output_ptrs_2)) = out_size)) (PreH10 : (start = (-1))) (PreH11 : (sep = 32)) (PreH12 : (sep = 32)) (PreH13 : ((contains_zb_125 (str_l) (32)) = true)) (PreH14 : (valid_string str_l )) (PreH15 : (all_ascii str_l )) (PreH16 : (valid_split_words_input_125 str_l )) (PreH17 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH18 : (problem_125_pre_z str_l )) (PreH19 : (output_rows_2 = (split_output_rows_125 (str_l) (sep)))) (PreH20 : (problem_125_spec_z str_l output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data_2 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data_2 out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs_2 output_rows_2 )
|--
  EX (output_rows: (@list (@list Z)))  (output_ptrs: (@list Z))  (data: Z) ,
  “ (out <> 0) ”
  &&  “ (data <> 0) ”
  &&  “ ((Zlength (output_ptrs)) = (Zlength (output_rows))) ”
  &&  “ ((Zlength (output_rows)) <= ((string_length (str_l)) + 1 )) ”
  &&  “ (problem_125_spec_z str_l output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows)))
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
) \/
(
forall (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (n: Z) (out: Z) (data_2: Z) (ch: Z) (len: Z) (out_size: Z) (start: Z) (sep: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (n = (string_length (str_l)))) (PreH3 : (out <> 0)) (PreH4 : (data_2 <> 0)) (PreH5 : (0 <= ch)) (PreH6 : (ch <= 127)) (PreH7 : (0 <= len)) (PreH8 : (len < INT_MAX)) (PreH9 : (out_size = (Zlength (output_rows_2)))) (PreH10 : ((Zlength (output_ptrs_2)) = out_size)) (PreH11 : (start = (-1))) (PreH12 : (sep = 32)) (PreH13 : (sep = 32)) (PreH14 : ((contains_zb_125 (str_l) (32)) = true)) (PreH15 : (valid_string str_l )) (PreH16 : (all_ascii str_l )) (PreH17 : (valid_split_words_input_125 str_l )) (PreH18 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH19 : (problem_125_pre_z str_l )) (PreH20 : (output_rows_2 = (split_output_rows_125 (str_l) (sep)))) (PreH21 : (problem_125_spec_z str_l output_rows_2 )) ,
  (PtrArray.seg data_2 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data_2 out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs_2 output_rows_2 )
|--
  EX (output_rows: (@list (@list Z)))  (output_ptrs: (@list Z)) ,
  “ (out_size = (Zlength (output_rows))) ”
  &&  “ (out <> 0) ”
  &&  “ (data_2 <> 0) ”
  &&  “ ((Zlength (output_ptrs)) = (Zlength (output_rows))) ”
  &&  “ ((Zlength (output_rows)) <= ((string_length (str_l)) + 1 )) ”
  &&  “ (problem_125_spec_z str_l output_rows ) ”
  &&  (PtrArray.seg data_2 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data_2 (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
).

Definition split_words_return_wit_4 :=
(
forall (txt_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (n: Z) (out: Z) (data_2: Z) (ch: Z) (len: Z) (out_size: Z) (start: Z) (sep: Z) (PreH1 : (n = (string_length (str_l)))) (PreH2 : (out <> 0)) (PreH3 : (data_2 <> 0)) (PreH4 : (0 <= ch)) (PreH5 : (ch <= 127)) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (out_size = (Zlength (output_rows_2)))) (PreH9 : ((Zlength (output_ptrs_2)) = out_size)) (PreH10 : (start = (-1))) (PreH11 : (sep = 44)) (PreH12 : (sep = 44)) (PreH13 : ((contains_zb_125 (str_l) (32)) = false)) (PreH14 : ((contains_zb_125 (str_l) (44)) = true)) (PreH15 : (valid_string str_l )) (PreH16 : (all_ascii str_l )) (PreH17 : (valid_split_words_input_125 str_l )) (PreH18 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH19 : (problem_125_pre_z str_l )) (PreH20 : (output_rows_2 = (split_output_rows_125 (str_l) (sep)))) (PreH21 : (problem_125_spec_z str_l output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data_2 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data_2 out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs_2 output_rows_2 )
|--
  EX (output_rows: (@list (@list Z)))  (output_ptrs: (@list Z))  (data: Z) ,
  “ (out <> 0) ”
  &&  “ (data <> 0) ”
  &&  “ ((Zlength (output_ptrs)) = (Zlength (output_rows))) ”
  &&  “ ((Zlength (output_rows)) <= ((string_length (str_l)) + 1 )) ”
  &&  “ (problem_125_spec_z str_l output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows)))
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
) \/
(
forall (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (n: Z) (out: Z) (data_2: Z) (ch: Z) (len: Z) (out_size: Z) (start: Z) (sep: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (n = (string_length (str_l)))) (PreH3 : (out <> 0)) (PreH4 : (data_2 <> 0)) (PreH5 : (0 <= ch)) (PreH6 : (ch <= 127)) (PreH7 : (0 <= len)) (PreH8 : (len < INT_MAX)) (PreH9 : (out_size = (Zlength (output_rows_2)))) (PreH10 : ((Zlength (output_ptrs_2)) = out_size)) (PreH11 : (start = (-1))) (PreH12 : (sep = 44)) (PreH13 : (sep = 44)) (PreH14 : ((contains_zb_125 (str_l) (32)) = false)) (PreH15 : ((contains_zb_125 (str_l) (44)) = true)) (PreH16 : (valid_string str_l )) (PreH17 : (all_ascii str_l )) (PreH18 : (valid_split_words_input_125 str_l )) (PreH19 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH20 : (problem_125_pre_z str_l )) (PreH21 : (output_rows_2 = (split_output_rows_125 (str_l) (sep)))) (PreH22 : (problem_125_spec_z str_l output_rows_2 )) ,
  (PtrArray.seg data_2 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data_2 out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs_2 output_rows_2 )
|--
  EX (output_rows: (@list (@list Z)))  (output_ptrs: (@list Z)) ,
  “ (out_size = (Zlength (output_rows))) ”
  &&  “ (out <> 0) ”
  &&  “ (data_2 <> 0) ”
  &&  “ ((Zlength (output_ptrs)) = (Zlength (output_rows))) ”
  &&  “ ((Zlength (output_rows)) <= ((string_length (str_l)) + 1 )) ”
  &&  “ (problem_125_spec_z str_l output_rows ) ”
  &&  (PtrArray.seg data_2 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data_2 (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
).

Definition split_words_return_wit_5 :=
forall (txt_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (n: Z) (out: Z) (data_2: Z) (ch: Z) (len: Z) (out_size: Z) (start: Z) (sep: Z) (PreH1 : (n = (string_length (str_l)))) (PreH2 : (out <> 0)) (PreH3 : (data_2 <> 0)) (PreH4 : (0 <= ch)) (PreH5 : (ch <= 127)) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (out_size = (Zlength (output_rows_2)))) (PreH9 : ((Zlength (output_ptrs_2)) = out_size)) (PreH10 : (start = (-1))) (PreH11 : (sep = 44)) (PreH12 : (sep = 32)) (PreH13 : ((contains_zb_125 (str_l) (32)) = true)) (PreH14 : (valid_string str_l )) (PreH15 : (all_ascii str_l )) (PreH16 : (valid_split_words_input_125 str_l )) (PreH17 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH18 : (problem_125_pre_z str_l )) (PreH19 : (output_rows_2 = (split_output_rows_125 (str_l) (sep)))) (PreH20 : (problem_125_spec_z str_l output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data_2 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data_2 out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs_2 output_rows_2 )
|--
  EX (output_rows: (@list (@list Z)))  (output_ptrs: (@list Z))  (data: Z) ,
  “ (out <> 0) ”
  &&  “ (data <> 0) ”
  &&  “ ((Zlength (output_ptrs)) = (Zlength (output_rows))) ”
  &&  “ ((Zlength (output_rows)) <= ((string_length (str_l)) + 1 )) ”
  &&  “ (problem_125_spec_z str_l output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows)))
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
.

Definition split_words_partial_solve_wit_1_pure :=
forall (txt_pre: Z) (str_l: (@list Z)) (PreH1 : (valid_string str_l )) (PreH2 : (all_ascii str_l )) (PreH3 : (valid_split_words_input_125 str_l )) (PreH4 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH5 : (problem_125_pre_z str_l )) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> 0)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  (store_string txt_pre str_l )
|--
  “ (valid_string str_l ) ”
  &&  “ ((string_length (str_l)) < INT_MAX) ”
.

Definition split_words_partial_solve_wit_1_aux :=
forall (txt_pre: Z) (str_l: (@list Z)) (PreH1 : (valid_string str_l )) (PreH2 : (all_ascii str_l )) (PreH3 : (valid_split_words_input_125 str_l )) (PreH4 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH5 : (problem_125_pre_z str_l )) ,
  (store_string txt_pre str_l )
|--
  “ (valid_string str_l ) ”
  &&  “ ((string_length (str_l)) < INT_MAX) ”
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  (store_string txt_pre str_l )
.

Definition split_words_partial_solve_wit_1 := split_words_partial_solve_wit_1_pure -> split_words_partial_solve_wit_1_aux.

Definition split_words_partial_solve_wit_2_pure :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (valid_string str_l )) (PreH4 : (all_ascii str_l )) (PreH5 : (valid_split_words_input_125 str_l )) (PreH6 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH7 : (problem_125_pre_z str_l )) ,
  ((( &( "space_hit" ) )) # Ptr  |->_)
  **  (store_string txt_pre str_l )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "data" ) )) # Ptr  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> 0)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (valid_string str_l ) ”
  &&  “ (0 <= 32) ”
  &&  “ (32 <= 127) ”
  &&  “ ((string_length (str_l)) < INT_MAX) ”
.

Definition split_words_partial_solve_wit_2_aux :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (valid_string str_l )) (PreH4 : (all_ascii str_l )) (PreH5 : (valid_split_words_input_125 str_l )) (PreH6 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH7 : (problem_125_pre_z str_l )) ,
  (store_string txt_pre str_l )
|--
  “ (valid_string str_l ) ”
  &&  “ (0 <= 32) ”
  &&  “ (32 <= 127) ”
  &&  “ ((string_length (str_l)) < INT_MAX) ”
  &&  “ (retval = (string_length (str_l))) ”
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  (store_string txt_pre str_l )
.

Definition split_words_partial_solve_wit_2 := split_words_partial_solve_wit_2_pure -> split_words_partial_solve_wit_2_aux.

Definition split_words_partial_solve_wit_3_pure :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH2 : (retval = (string_length (str_l)))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (valid_string str_l )) (PreH5 : (all_ascii str_l )) (PreH6 : (valid_split_words_input_125 str_l )) (PreH7 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH8 : (problem_125_pre_z str_l )) ,
  ((( &( "comma_hit" ) )) # Ptr  |->_)
  **  (store_string txt_pre str_l )
  **  ((( &( "space_hit" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "data" ) )) # Ptr  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> 0)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (valid_string str_l ) ”
  &&  “ (0 <= 44) ”
  &&  “ (44 <= 127) ”
  &&  “ ((string_length (str_l)) < INT_MAX) ”
.

Definition split_words_partial_solve_wit_3_aux :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH2 : (retval = (string_length (str_l)))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (valid_string str_l )) (PreH5 : (all_ascii str_l )) (PreH6 : (valid_split_words_input_125 str_l )) (PreH7 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH8 : (problem_125_pre_z str_l )) ,
  (store_string txt_pre str_l )
|--
  “ (valid_string str_l ) ”
  &&  “ (0 <= 44) ”
  &&  “ (44 <= 127) ”
  &&  “ ((string_length (str_l)) < INT_MAX) ”
  &&  “ (strchr_result str_l 32 retval_2 txt_pre ) ”
  &&  “ (retval = (string_length (str_l))) ”
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  (store_string txt_pre str_l )
.

Definition split_words_partial_solve_wit_3 := split_words_partial_solve_wit_3_pure -> split_words_partial_solve_wit_3_aux.

Definition split_words_partial_solve_wit_4 :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (strchr_result str_l 44 retval_3 txt_pre )) (PreH2 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (valid_split_words_input_125 str_l )) (PreH8 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH9 : (problem_125_pre_z str_l )) ,
  (store_string txt_pre str_l )
|--
  “ (strchr_result str_l 44 retval_3 txt_pre ) ”
  &&  “ (strchr_result str_l 32 retval_2 txt_pre ) ”
  &&  “ (retval = (string_length (str_l))) ”
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
.

Definition split_words_partial_solve_wit_5_pure :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (strchr_result str_l 44 retval_3 txt_pre )) (PreH3 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH4 : (retval = (string_length (str_l)))) (PreH5 : (0 <= ((string_length (str_l)) + 1 ))) (PreH6 : (valid_string str_l )) (PreH7 : (all_ascii str_l )) (PreH8 : (valid_split_words_input_125 str_l )) (PreH9 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH10 : (problem_125_pre_z str_l )) ,
  ((&((retval_4)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "comma_hit" ) )) # Ptr  |-> retval_3)
  **  ((( &( "space_hit" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "data" ) )) # Ptr  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval_4)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (0 <= (retval + 1 )) ”
  &&  “ ((retval + 1 ) < INT_MAX) ”
.

Definition split_words_partial_solve_wit_5_aux :=
forall (txt_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (strchr_result str_l 44 retval_3 txt_pre )) (PreH3 : (strchr_result str_l 32 retval_2 txt_pre )) (PreH4 : (retval = (string_length (str_l)))) (PreH5 : (0 <= ((string_length (str_l)) + 1 ))) (PreH6 : (valid_string str_l )) (PreH7 : (all_ascii str_l )) (PreH8 : (valid_split_words_input_125 str_l )) (PreH9 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH10 : (problem_125_pre_z str_l )) ,
  ((&((retval_4)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
|--
  “ (0 <= (retval + 1 )) ”
  &&  “ ((retval + 1 ) < INT_MAX) ”
  &&  “ (retval_4 <> 0) ”
  &&  “ (strchr_result str_l 44 retval_3 txt_pre ) ”
  &&  “ (strchr_result str_l 32 retval_2 txt_pre ) ”
  &&  “ (retval = (string_length (str_l))) ”
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  ((&((retval_4)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_4)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
.

Definition split_words_partial_solve_wit_5 := split_words_partial_solve_wit_5_pure -> split_words_partial_solve_wit_5_aux.

Definition split_words_partial_solve_wit_6 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = sep)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (sep = 44)) (PreH16 : (sep = 44)) (PreH17 : ((contains_zb_125 (str_l) (32)) = false)) (PreH18 : ((contains_zb_125 (str_l) (44)) = true)) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : (0 <= len)) (PreH22 : (len < INT_MAX)) (PreH23 : (valid_string str_l )) (PreH24 : (all_ascii str_l )) (PreH25 : (valid_split_words_input_125 str_l )) (PreH26 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH27 : (problem_125_pre_z str_l )) (PreH28 : (split_scan_state_125 str_l i start sep output_rows )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ (0 <= ((string_length (str_l)) + 1 )) ”
  &&  “ (start >= 0) ”
  &&  “ ((Znth i (c_string (str_l)) 0) = sep) ”
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l i start sep output_rows ) ”
  &&  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
.

Definition split_words_partial_solve_wit_7 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = sep)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (sep = 32)) (PreH16 : (sep = 32)) (PreH17 : ((contains_zb_125 (str_l) (32)) = true)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_split_words_input_125 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_125_pre_z str_l )) (PreH27 : (split_scan_state_125 str_l i start sep output_rows )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ (0 <= ((string_length (str_l)) + 1 )) ”
  &&  “ (start >= 0) ”
  &&  “ ((Znth i (c_string (str_l)) 0) = sep) ”
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l i start sep output_rows ) ”
  &&  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
.

Definition split_words_partial_solve_wit_8 :=
forall (txt_pre: Z) (str_l: (@list Z)) (k: Z) (sep: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (k < len)) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (0 <= start)) (PreH13 : (start < i)) (PreH14 : (len = (i - start ))) (PreH15 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH16 : (ch = sep)) (PreH17 : (sep = 44)) (PreH18 : (sep = 44)) (PreH19 : ((contains_zb_125 (str_l) (32)) = false)) (PreH20 : ((contains_zb_125 (str_l) (44)) = true)) (PreH21 : (0 <= ch)) (PreH22 : (ch <= 127)) (PreH23 : (0 <= k)) (PreH24 : (k <= len)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_split_words_input_125 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_125_pre_z str_l )) (PreH30 : (split_scan_state_125 str_l i start sep output_rows )) (PreH31 : ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i)))) (PreH32 : ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_125 (str_l) (start) ((start + k ))) )
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
  &&  “ (ch = sep) ”
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= len) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l i start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len) ”
  &&  (((w + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.undef_missing_i w k k (len + 1 ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_125 (str_l) (start) ((start + k ))) )
.

Definition split_words_partial_solve_wit_9 :=
forall (txt_pre: Z) (str_l: (@list Z)) (k: Z) (sep: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (k < len)) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (0 <= start)) (PreH13 : (start < i)) (PreH14 : (len = (i - start ))) (PreH15 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH16 : (ch = sep)) (PreH17 : (sep = 32)) (PreH18 : (sep = 32)) (PreH19 : ((contains_zb_125 (str_l) (32)) = true)) (PreH20 : (0 <= ch)) (PreH21 : (ch <= 127)) (PreH22 : (0 <= k)) (PreH23 : (k <= len)) (PreH24 : (valid_string str_l )) (PreH25 : (all_ascii str_l )) (PreH26 : (valid_split_words_input_125 str_l )) (PreH27 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH28 : (problem_125_pre_z str_l )) (PreH29 : (split_scan_state_125 str_l i start sep output_rows )) (PreH30 : ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i)))) (PreH31 : ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_125 (str_l) (start) ((start + k ))) )
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
  &&  “ (ch = sep) ”
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= len) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l i start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len) ”
  &&  (((w + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.undef_missing_i w k k (len + 1 ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_125 (str_l) (start) ((start + k ))) )
.

Definition split_words_partial_solve_wit_10 :=
forall (txt_pre: Z) (str_l: (@list Z)) (k: Z) (sep: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (k >= len)) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (0 <= start)) (PreH13 : (start < i)) (PreH14 : (len = (i - start ))) (PreH15 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH16 : (ch = sep)) (PreH17 : (sep = 44)) (PreH18 : (sep = 44)) (PreH19 : ((contains_zb_125 (str_l) (32)) = false)) (PreH20 : ((contains_zb_125 (str_l) (44)) = true)) (PreH21 : (0 <= ch)) (PreH22 : (ch <= 127)) (PreH23 : (0 <= k)) (PreH24 : (k <= len)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_split_words_input_125 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_125_pre_z str_l )) (PreH30 : (split_scan_state_125 str_l i start sep output_rows )) (PreH31 : ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i)))) (PreH32 : ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_125 (str_l) (start) ((start + k ))) )
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
  &&  “ (ch = sep) ”
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= len) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l i start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len) ”
  &&  (((w + (len * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.undef_missing_i w len k (len + 1 ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_125 (str_l) (start) ((start + k ))) )
.

Definition split_words_partial_solve_wit_11 :=
forall (txt_pre: Z) (str_l: (@list Z)) (k: Z) (sep: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (k >= len)) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (0 <= start)) (PreH13 : (start < i)) (PreH14 : (len = (i - start ))) (PreH15 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH16 : (ch = sep)) (PreH17 : (sep = 32)) (PreH18 : (sep = 32)) (PreH19 : ((contains_zb_125 (str_l) (32)) = true)) (PreH20 : (0 <= ch)) (PreH21 : (ch <= 127)) (PreH22 : (0 <= k)) (PreH23 : (k <= len)) (PreH24 : (valid_string str_l )) (PreH25 : (all_ascii str_l )) (PreH26 : (valid_split_words_input_125 str_l )) (PreH27 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH28 : (problem_125_pre_z str_l )) (PreH29 : (split_scan_state_125 str_l i start sep output_rows )) (PreH30 : ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i)))) (PreH31 : ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_125 (str_l) (start) ((start + k ))) )
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
  &&  “ (ch = sep) ”
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= len) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l i start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len) ”
  &&  (((w + (len * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.undef_missing_i w len k (len + 1 ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_125 (str_l) (start) ((start + k ))) )
.

Definition split_words_partial_solve_wit_12 :=
forall (txt_pre: Z) (str_l: (@list Z)) (k: Z) (sep: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (k >= len)) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (w <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : (0 <= start)) (PreH14 : (start < i)) (PreH15 : (len = (i - start ))) (PreH16 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH17 : (ch = sep)) (PreH18 : (sep = 44)) (PreH19 : (sep = 44)) (PreH20 : ((contains_zb_125 (str_l) (32)) = false)) (PreH21 : ((contains_zb_125 (str_l) (44)) = true)) (PreH22 : (0 <= ch)) (PreH23 : (ch <= 127)) (PreH24 : (0 <= k)) (PreH25 : (k <= len)) (PreH26 : (valid_string str_l )) (PreH27 : (all_ascii str_l )) (PreH28 : (valid_split_words_input_125 str_l )) (PreH29 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH30 : (problem_125_pre_z str_l )) (PreH31 : (split_scan_state_125 str_l i start sep output_rows )) (PreH32 : ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i)))) (PreH33 : ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len)) ,
  (CharArray.full w (k + 1 ) (app ((word_payload_125 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg w (len + 1 ) (len + 1 ) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ (0 <= (k + 1 )) ”
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ”
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
  &&  “ (ch = sep) ”
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= len) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l i start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len) ”
  &&  (((data + (out_size * sizeof(PTR) ) )) # Ptr  |->_)
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full w (k + 1 ) (app ((word_payload_125 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
.

Definition split_words_partial_solve_wit_13 :=
forall (txt_pre: Z) (str_l: (@list Z)) (k: Z) (sep: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (k >= len)) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (w <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : (0 <= start)) (PreH14 : (start < i)) (PreH15 : (len = (i - start ))) (PreH16 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH17 : (ch = sep)) (PreH18 : (sep = 32)) (PreH19 : (sep = 32)) (PreH20 : ((contains_zb_125 (str_l) (32)) = true)) (PreH21 : (0 <= ch)) (PreH22 : (ch <= 127)) (PreH23 : (0 <= k)) (PreH24 : (k <= len)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_split_words_input_125 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_125_pre_z str_l )) (PreH30 : (split_scan_state_125 str_l i start sep output_rows )) (PreH31 : ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i)))) (PreH32 : ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len)) ,
  (CharArray.full w (k + 1 ) (app ((word_payload_125 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg w (len + 1 ) (len + 1 ) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ (0 <= (k + 1 )) ”
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ”
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
  &&  “ (ch = sep) ”
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= len) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l i start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (i) (sep)) = (word_payload_125 (str_l) (start) (i))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (i)))) = len) ”
  &&  (((data + (out_size * sizeof(PTR) ) )) # Ptr  |->_)
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full w (k + 1 ) (app ((word_payload_125 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
.

Definition split_words_partial_solve_wit_14 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : (i >= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : ((-1) <= start)) (PreH13 : (start < i)) (PreH14 : (sep = 44)) (PreH15 : (sep = 44)) (PreH16 : ((contains_zb_125 (str_l) (32)) = false)) (PreH17 : ((contains_zb_125 (str_l) (44)) = true)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_split_words_input_125 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_125_pre_z str_l )) (PreH27 : (split_scan_state_125 str_l i start sep output_rows )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ (0 <= ((string_length (str_l)) + 1 )) ”
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l i start sep output_rows ) ”
  &&  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
.

Definition split_words_partial_solve_wit_15 :=
forall (txt_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (sep: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : (i >= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : ((-1) <= start)) (PreH13 : (start < i)) (PreH14 : (sep = 32)) (PreH15 : (sep = 32)) (PreH16 : ((contains_zb_125 (str_l) (32)) = true)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_split_words_input_125 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_125_pre_z str_l )) (PreH26 : (split_scan_state_125 str_l i start sep output_rows )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
|--
  “ (0 <= ((string_length (str_l)) + 1 )) ”
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (0 <= ch) ”
  &&  “ (ch <= 127) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l i start sep output_rows ) ”
  &&  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
.

Definition split_words_partial_solve_wit_16 :=
forall (txt_pre: Z) (str_l: (@list Z)) (sep: Z) (k: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (k < len)) (PreH2 : (n = (string_length (str_l)))) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (w <> 0)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= n)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (0 <= start)) (PreH13 : (start < n)) (PreH14 : (len = (n - start ))) (PreH15 : (0 <= k)) (PreH16 : (k <= len)) (PreH17 : (sep = 44)) (PreH18 : (sep = 44)) (PreH19 : ((contains_zb_125 (str_l) (32)) = false)) (PreH20 : ((contains_zb_125 (str_l) (44)) = true)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_split_words_input_125 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_125_pre_z str_l )) (PreH26 : (split_scan_state_125 str_l n start sep output_rows )) (PreH27 : ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n)))) (PreH28 : ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_125 (str_l) (start) ((start + k ))) )
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l n start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len) ”
  &&  (((w + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.undef_missing_i w k k (len + 1 ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_125 (str_l) (start) ((start + k ))) )
.

Definition split_words_partial_solve_wit_17 :=
forall (txt_pre: Z) (str_l: (@list Z)) (sep: Z) (k: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (k < len)) (PreH2 : (n = (string_length (str_l)))) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (w <> 0)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= n)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (0 <= start)) (PreH13 : (start < n)) (PreH14 : (len = (n - start ))) (PreH15 : (0 <= k)) (PreH16 : (k <= len)) (PreH17 : (sep = 32)) (PreH18 : (sep = 32)) (PreH19 : ((contains_zb_125 (str_l) (32)) = true)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_split_words_input_125 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_125_pre_z str_l )) (PreH25 : (split_scan_state_125 str_l n start sep output_rows )) (PreH26 : ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n)))) (PreH27 : ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_125 (str_l) (start) ((start + k ))) )
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l n start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len) ”
  &&  (((w + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.undef_missing_i w k k (len + 1 ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_125 (str_l) (start) ((start + k ))) )
.

Definition split_words_partial_solve_wit_18 :=
forall (txt_pre: Z) (str_l: (@list Z)) (sep: Z) (k: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (k >= len)) (PreH2 : (n = (string_length (str_l)))) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (w <> 0)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= n)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (0 <= start)) (PreH13 : (start < n)) (PreH14 : (len = (n - start ))) (PreH15 : (0 <= k)) (PreH16 : (k <= len)) (PreH17 : (sep = 44)) (PreH18 : (sep = 44)) (PreH19 : ((contains_zb_125 (str_l) (32)) = false)) (PreH20 : ((contains_zb_125 (str_l) (44)) = true)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_split_words_input_125 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_125_pre_z str_l )) (PreH26 : (split_scan_state_125 str_l n start sep output_rows )) (PreH27 : ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n)))) (PreH28 : ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_125 (str_l) (start) ((start + k ))) )
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l n start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len) ”
  &&  (((w + (len * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.undef_missing_i w len k (len + 1 ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_125 (str_l) (start) ((start + k ))) )
.

Definition split_words_partial_solve_wit_19 :=
forall (txt_pre: Z) (str_l: (@list Z)) (sep: Z) (k: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (k >= len)) (PreH2 : (n = (string_length (str_l)))) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (w <> 0)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= n)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (0 <= start)) (PreH13 : (start < n)) (PreH14 : (len = (n - start ))) (PreH15 : (0 <= k)) (PreH16 : (k <= len)) (PreH17 : (sep = 32)) (PreH18 : (sep = 32)) (PreH19 : ((contains_zb_125 (str_l) (32)) = true)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_split_words_input_125 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_125_pre_z str_l )) (PreH25 : (split_scan_state_125 str_l n start sep output_rows )) (PreH26 : ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n)))) (PreH27 : ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string txt_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_125 (str_l) (start) ((start + k ))) )
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l n start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len) ”
  &&  (((w + (len * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.undef_missing_i w len k (len + 1 ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_125 (str_l) (start) ((start + k ))) )
.

Definition split_words_partial_solve_wit_20 :=
forall (txt_pre: Z) (str_l: (@list Z)) (sep: Z) (k: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (k >= len)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (w <> 0)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= n)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : (0 <= start)) (PreH14 : (start < n)) (PreH15 : (len = (n - start ))) (PreH16 : (0 <= k)) (PreH17 : (k <= len)) (PreH18 : (sep = 44)) (PreH19 : (sep = 44)) (PreH20 : ((contains_zb_125 (str_l) (32)) = false)) (PreH21 : ((contains_zb_125 (str_l) (44)) = true)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_split_words_input_125 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_125_pre_z str_l )) (PreH27 : (split_scan_state_125 str_l n start sep output_rows )) (PreH28 : ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n)))) (PreH29 : ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len)) ,
  (CharArray.full w (k + 1 ) (app ((word_payload_125 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg w (len + 1 ) (len + 1 ) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
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
  &&  “ (sep = 44) ”
  &&  “ (sep = 44) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = true) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l n start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len) ”
  &&  (((data + (out_size * sizeof(PTR) ) )) # Ptr  |->_)
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full w (k + 1 ) (app ((word_payload_125 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
.

Definition split_words_partial_solve_wit_21 :=
forall (txt_pre: Z) (str_l: (@list Z)) (sep: Z) (k: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (k >= len)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (w <> 0)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= n)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : (0 <= start)) (PreH14 : (start < n)) (PreH15 : (len = (n - start ))) (PreH16 : (0 <= k)) (PreH17 : (k <= len)) (PreH18 : (sep = 32)) (PreH19 : (sep = 32)) (PreH20 : ((contains_zb_125 (str_l) (32)) = true)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_split_words_input_125 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_125_pre_z str_l )) (PreH26 : (split_scan_state_125 str_l n start sep output_rows )) (PreH27 : ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n)))) (PreH28 : ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len)) ,
  (CharArray.full w (k + 1 ) (app ((word_payload_125 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg w (len + 1 ) (len + 1 ) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
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
  &&  “ (sep = 32) ”
  &&  “ (sep = 32) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = true) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  “ (split_scan_state_125 str_l n start sep output_rows ) ”
  &&  “ ((split_scan_current_125 (str_l) (n) (sep)) = (word_payload_125 (str_l) (start) (n))) ”
  &&  “ ((Zlength ((word_payload_125 (str_l) (start) (n)))) = len) ”
  &&  (((data + (out_size * sizeof(PTR) ) )) # Ptr  |->_)
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full w (k + 1 ) (app ((word_payload_125 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (split_words_rows_heap_125 output_ptrs output_rows )
.

Definition split_words_partial_solve_wit_22_pure :=
forall (txt_pre: Z) (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (i >= n)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (0 <= len)) (PreH11 : (len < INT_MAX)) (PreH12 : (space_hit = 0)) (PreH13 : (comma_hit = 0)) (PreH14 : ((contains_zb_125 (str_l) (32)) = false)) (PreH15 : ((contains_zb_125 (str_l) (44)) = false)) (PreH16 : (valid_string str_l )) (PreH17 : (all_ascii str_l )) (PreH18 : (valid_split_words_input_125 str_l )) (PreH19 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH20 : (problem_125_pre_z str_l )) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string txt_pre str_l )
  **  (PtrArray.undef_full data (n + 1 ) )
|--
  “ (0 <= out_size) ”
  &&  “ (out_size < INT_MAX) ”
.

Definition split_words_partial_solve_wit_22_aux :=
forall (txt_pre: Z) (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (i >= n)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (0 <= len)) (PreH11 : (len < INT_MAX)) (PreH12 : (space_hit = 0)) (PreH13 : (comma_hit = 0)) (PreH14 : ((contains_zb_125 (str_l) (32)) = false)) (PreH15 : ((contains_zb_125 (str_l) (44)) = false)) (PreH16 : (valid_string str_l )) (PreH17 : (all_ascii str_l )) (PreH18 : (valid_split_words_input_125 str_l )) (PreH19 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH20 : (problem_125_pre_z str_l )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string txt_pre str_l )
  **  (PtrArray.undef_full data (n + 1 ) )
|--
  “ (0 <= out_size) ”
  &&  “ (out_size < INT_MAX) ”
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ”
  &&  “ (i >= n) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n) ”
  &&  “ (n = (string_length (str_l))) ”
  &&  “ (out <> 0) ”
  &&  “ (data <> 0) ”
  &&  “ (out_size = (odd_lower_prefix_125 (str_l) (i))) ”
  &&  “ (0 <= out_size) ”
  &&  “ (out_size <= i) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (space_hit = 0) ”
  &&  “ (comma_hit = 0) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = false) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (PtrArray.undef_full data (n + 1 ) )
.

Definition split_words_partial_solve_wit_22 := split_words_partial_solve_wit_22_pure -> split_words_partial_solve_wit_22_aux.

Definition split_words_partial_solve_wit_23 :=
forall (txt_pre: Z) (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (1 <= retval)) (PreH2 : (retval < INT_MAX)) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (i >= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (0 <= len)) (PreH14 : (len < INT_MAX)) (PreH15 : (space_hit = 0)) (PreH16 : (comma_hit = 0)) (PreH17 : ((contains_zb_125 (str_l) (32)) = false)) (PreH18 : ((contains_zb_125 (str_l) (44)) = false)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_split_words_input_125 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_125_pre_z str_l )) ,
  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (PtrArray.undef_full data (n + 1 ) )
|--
  “ (1 <= retval) ”
  &&  “ (retval < INT_MAX) ”
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ”
  &&  “ (i >= n) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n) ”
  &&  “ (n = (string_length (str_l))) ”
  &&  “ (out <> 0) ”
  &&  “ (data <> 0) ”
  &&  “ (out_size = (odd_lower_prefix_125 (str_l) (i))) ”
  &&  “ (0 <= out_size) ”
  &&  “ (out_size <= i) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (space_hit = 0) ”
  &&  “ (comma_hit = 0) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = false) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (PtrArray.undef_full data (n + 1 ) )
.

Definition split_words_partial_solve_wit_24_pure :=
forall (txt_pre: Z) (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (1 <= retval)) (PreH3 : (retval < INT_MAX)) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (i >= n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (0 <= len)) (PreH15 : (len < INT_MAX)) (PreH16 : (space_hit = 0)) (PreH17 : (comma_hit = 0)) (PreH18 : ((contains_zb_125 (str_l) (32)) = false)) (PreH19 : ((contains_zb_125 (str_l) (44)) = false)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_split_words_input_125 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_125_pre_z str_l )) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> retval_2)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "space_hit" ) )) # Ptr  |-> space_hit)
  **  ((( &( "comma_hit" ) )) # Ptr  |-> comma_hit)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (PtrArray.undef_full data (n + 1 ) )
|--
  “ (0 <= out_size) ”
  &&  “ (out_size < INT_MAX) ”
  &&  “ (1 <= retval) ”
  &&  “ (retval < INT_MAX) ”
.

Definition split_words_partial_solve_wit_24_aux :=
forall (txt_pre: Z) (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (1 <= retval)) (PreH3 : (retval < INT_MAX)) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (i >= n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (0 <= len)) (PreH15 : (len < INT_MAX)) (PreH16 : (space_hit = 0)) (PreH17 : (comma_hit = 0)) (PreH18 : ((contains_zb_125 (str_l) (32)) = false)) (PreH19 : ((contains_zb_125 (str_l) (44)) = false)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_split_words_input_125 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_125_pre_z str_l )) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (PtrArray.undef_full data (n + 1 ) )
|--
  “ (0 <= out_size) ”
  &&  “ (out_size < INT_MAX) ”
  &&  “ (1 <= retval) ”
  &&  “ (retval < INT_MAX) ”
  &&  “ (retval_2 <> 0) ”
  &&  “ (1 <= retval) ”
  &&  “ (retval < INT_MAX) ”
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ”
  &&  “ (i >= n) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n) ”
  &&  “ (n = (string_length (str_l))) ”
  &&  “ (out <> 0) ”
  &&  “ (data <> 0) ”
  &&  “ (out_size = (odd_lower_prefix_125 (str_l) (i))) ”
  &&  “ (0 <= out_size) ”
  &&  “ (out_size <= i) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (space_hit = 0) ”
  &&  “ (comma_hit = 0) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = false) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (PtrArray.undef_full data (n + 1 ) )
.

Definition split_words_partial_solve_wit_24 := split_words_partial_solve_wit_24_pure -> split_words_partial_solve_wit_24_aux.

Definition split_words_partial_solve_wit_25 :=
forall (txt_pre: Z) (str_l: (@list Z)) (comma_hit: Z) (space_hit: Z) (len: Z) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (retval_2: Z) (out_l: (@list Z)) (PreH1 : ((Zlength (out_l)) = retval)) (PreH2 : (retval_2 <> 0)) (PreH3 : (1 <= retval)) (PreH4 : (retval < INT_MAX)) (PreH5 : (0 <= ((string_length (str_l)) + 1 ))) (PreH6 : (i >= n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (n = (string_length (str_l)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (out_size = (odd_lower_prefix_125 (str_l) (i)))) (PreH13 : (0 <= out_size)) (PreH14 : (out_size <= i)) (PreH15 : (0 <= len)) (PreH16 : (len < INT_MAX)) (PreH17 : (space_hit = 0)) (PreH18 : (comma_hit = 0)) (PreH19 : ((contains_zb_125 (str_l) (32)) = false)) (PreH20 : ((contains_zb_125 (str_l) (44)) = false)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_split_words_input_125 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_125_pre_z str_l )) ,
  (CharArray.full retval_2 (retval + 1 ) (c_string (out_l)) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (PtrArray.undef_full data (n + 1 ) )
|--
  “ (0 <= (retval + 1 )) ”
  &&  “ ((Zlength (out_l)) = retval) ”
  &&  “ (retval_2 <> 0) ”
  &&  “ (1 <= retval) ”
  &&  “ (retval < INT_MAX) ”
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ”
  &&  “ (i >= n) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n) ”
  &&  “ (n = (string_length (str_l))) ”
  &&  “ (out <> 0) ”
  &&  “ (data <> 0) ”
  &&  “ (out_size = (odd_lower_prefix_125 (str_l) (i))) ”
  &&  “ (0 <= out_size) ”
  &&  “ (out_size <= i) ”
  &&  “ (0 <= len) ”
  &&  “ (len < INT_MAX) ”
  &&  “ (space_hit = 0) ”
  &&  “ (comma_hit = 0) ”
  &&  “ ((contains_zb_125 (str_l) (32)) = false) ”
  &&  “ ((contains_zb_125 (str_l) (44)) = false) ”
  &&  “ (valid_string str_l ) ”
  &&  “ (all_ascii str_l ) ”
  &&  “ (valid_split_words_input_125 str_l ) ”
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ”
  &&  “ (problem_125_pre_z str_l ) ”
  &&  (((data + (0 * sizeof(PTR) ) )) # Ptr  |->_)
  **  (PtrArray.undef_missing_i data 0 0 (n + 1 ) )
  **  (CharArray.full retval_2 (retval + 1 ) (c_string (out_l)) )
  **  (CharArray.full txt_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
.

Module Type VC_Correct.

Include ptr_array2_Strategy_Correct.
Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_decimal_len_safety_wit_1 : decimal_len_safety_wit_1.
Axiom proof_of_decimal_len_safety_wit_2 : decimal_len_safety_wit_2.
Axiom proof_of_decimal_len_safety_wit_3 : decimal_len_safety_wit_3.
Axiom proof_of_decimal_len_safety_wit_4 : decimal_len_safety_wit_4.
Axiom proof_of_decimal_len_safety_wit_5 : decimal_len_safety_wit_5.
Axiom proof_of_decimal_len_safety_wit_6 : decimal_len_safety_wit_6.
Axiom proof_of_decimal_len_safety_wit_7 : decimal_len_safety_wit_7.
Axiom proof_of_decimal_len_safety_wit_8 : decimal_len_safety_wit_8.
Axiom proof_of_decimal_len_safety_wit_9 : decimal_len_safety_wit_9.
Axiom proof_of_decimal_len_safety_wit_10 : decimal_len_safety_wit_10.
Axiom proof_of_decimal_len_safety_wit_11 : decimal_len_safety_wit_11.
Axiom proof_of_decimal_len_safety_wit_12 : decimal_len_safety_wit_12.
Axiom proof_of_decimal_len_safety_wit_13 : decimal_len_safety_wit_13.
Axiom proof_of_decimal_len_safety_wit_14 : decimal_len_safety_wit_14.
Axiom proof_of_decimal_len_safety_wit_15 : decimal_len_safety_wit_15.
Axiom proof_of_decimal_len_safety_wit_16 : decimal_len_safety_wit_16.
Axiom proof_of_decimal_len_safety_wit_17 : decimal_len_safety_wit_17.
Axiom proof_of_decimal_len_safety_wit_18 : decimal_len_safety_wit_18.
Axiom proof_of_decimal_len_safety_wit_19 : decimal_len_safety_wit_19.
Axiom proof_of_decimal_len_return_wit_1 : decimal_len_return_wit_1.
Axiom proof_of_decimal_len_return_wit_2 : decimal_len_return_wit_2.
Axiom proof_of_decimal_len_return_wit_3 : decimal_len_return_wit_3.
Axiom proof_of_decimal_len_return_wit_4 : decimal_len_return_wit_4.
Axiom proof_of_decimal_len_return_wit_5 : decimal_len_return_wit_5.
Axiom proof_of_decimal_len_return_wit_6 : decimal_len_return_wit_6.
Axiom proof_of_decimal_len_return_wit_7 : decimal_len_return_wit_7.
Axiom proof_of_decimal_len_return_wit_8 : decimal_len_return_wit_8.
Axiom proof_of_decimal_len_return_wit_9 : decimal_len_return_wit_9.
Axiom proof_of_decimal_len_return_wit_10 : decimal_len_return_wit_10.
Axiom proof_of_write_decimal_safety_wit_1 : write_decimal_safety_wit_1.
Axiom proof_of_write_decimal_safety_wit_2 : write_decimal_safety_wit_2.
Axiom proof_of_write_decimal_safety_wit_3 : write_decimal_safety_wit_3.
Axiom proof_of_write_decimal_safety_wit_4 : write_decimal_safety_wit_4.
Axiom proof_of_write_decimal_safety_wit_5 : write_decimal_safety_wit_5.
Axiom proof_of_write_decimal_safety_wit_6 : write_decimal_safety_wit_6.
Axiom proof_of_write_decimal_safety_wit_7 : write_decimal_safety_wit_7.
Axiom proof_of_write_decimal_safety_wit_8 : write_decimal_safety_wit_8.
Axiom proof_of_write_decimal_safety_wit_9 : write_decimal_safety_wit_9.
Axiom proof_of_write_decimal_safety_wit_10 : write_decimal_safety_wit_10.
Axiom proof_of_write_decimal_safety_wit_11 : write_decimal_safety_wit_11.
Axiom proof_of_write_decimal_entail_wit_1 : write_decimal_entail_wit_1.
Axiom proof_of_write_decimal_entail_wit_2 : write_decimal_entail_wit_2.
Axiom proof_of_write_decimal_return_wit_1 : write_decimal_return_wit_1.
Axiom proof_of_write_decimal_partial_solve_wit_1 : write_decimal_partial_solve_wit_1.
Axiom proof_of_write_decimal_partial_solve_wit_2 : write_decimal_partial_solve_wit_2.
Axiom proof_of_split_words_safety_wit_1 : split_words_safety_wit_1.
Axiom proof_of_split_words_safety_wit_2 : split_words_safety_wit_2.
Axiom proof_of_split_words_safety_wit_3 : split_words_safety_wit_3.
Axiom proof_of_split_words_safety_wit_4 : split_words_safety_wit_4.
Axiom proof_of_split_words_safety_wit_5 : split_words_safety_wit_5.
Axiom proof_of_split_words_safety_wit_6 : split_words_safety_wit_6.
Axiom proof_of_split_words_safety_wit_7 : split_words_safety_wit_7.
Axiom proof_of_split_words_safety_wit_8 : split_words_safety_wit_8.
Axiom proof_of_split_words_safety_wit_9 : split_words_safety_wit_9.
Axiom proof_of_split_words_safety_wit_10 : split_words_safety_wit_10.
Axiom proof_of_split_words_safety_wit_11 : split_words_safety_wit_11.
Axiom proof_of_split_words_safety_wit_12 : split_words_safety_wit_12.
Axiom proof_of_split_words_safety_wit_13 : split_words_safety_wit_13.
Axiom proof_of_split_words_safety_wit_14 : split_words_safety_wit_14.
Axiom proof_of_split_words_safety_wit_15 : split_words_safety_wit_15.
Axiom proof_of_split_words_safety_wit_16 : split_words_safety_wit_16.
Axiom proof_of_split_words_safety_wit_17 : split_words_safety_wit_17.
Axiom proof_of_split_words_safety_wit_18 : split_words_safety_wit_18.
Axiom proof_of_split_words_safety_wit_19 : split_words_safety_wit_19.
Axiom proof_of_split_words_safety_wit_20 : split_words_safety_wit_20.
Axiom proof_of_split_words_safety_wit_21 : split_words_safety_wit_21.
Axiom proof_of_split_words_safety_wit_22 : split_words_safety_wit_22.
Axiom proof_of_split_words_safety_wit_23 : split_words_safety_wit_23.
Axiom proof_of_split_words_safety_wit_24 : split_words_safety_wit_24.
Axiom proof_of_split_words_safety_wit_25 : split_words_safety_wit_25.
Axiom proof_of_split_words_safety_wit_26 : split_words_safety_wit_26.
Axiom proof_of_split_words_safety_wit_27 : split_words_safety_wit_27.
Axiom proof_of_split_words_safety_wit_28 : split_words_safety_wit_28.
Axiom proof_of_split_words_safety_wit_29 : split_words_safety_wit_29.
Axiom proof_of_split_words_safety_wit_30 : split_words_safety_wit_30.
Axiom proof_of_split_words_safety_wit_31 : split_words_safety_wit_31.
Axiom proof_of_split_words_safety_wit_32 : split_words_safety_wit_32.
Axiom proof_of_split_words_safety_wit_33 : split_words_safety_wit_33.
Axiom proof_of_split_words_safety_wit_34 : split_words_safety_wit_34.
Axiom proof_of_split_words_safety_wit_35 : split_words_safety_wit_35.
Axiom proof_of_split_words_safety_wit_36 : split_words_safety_wit_36.
Axiom proof_of_split_words_safety_wit_37 : split_words_safety_wit_37.
Axiom proof_of_split_words_safety_wit_38 : split_words_safety_wit_38.
Axiom proof_of_split_words_safety_wit_39 : split_words_safety_wit_39.
Axiom proof_of_split_words_safety_wit_40 : split_words_safety_wit_40.
Axiom proof_of_split_words_safety_wit_41 : split_words_safety_wit_41.
Axiom proof_of_split_words_safety_wit_42 : split_words_safety_wit_42.
Axiom proof_of_split_words_safety_wit_43 : split_words_safety_wit_43.
Axiom proof_of_split_words_safety_wit_44 : split_words_safety_wit_44.
Axiom proof_of_split_words_safety_wit_45 : split_words_safety_wit_45.
Axiom proof_of_split_words_safety_wit_46 : split_words_safety_wit_46.
Axiom proof_of_split_words_safety_wit_47 : split_words_safety_wit_47.
Axiom proof_of_split_words_safety_wit_48 : split_words_safety_wit_48.
Axiom proof_of_split_words_safety_wit_49 : split_words_safety_wit_49.
Axiom proof_of_split_words_safety_wit_50 : split_words_safety_wit_50.
Axiom proof_of_split_words_safety_wit_51 : split_words_safety_wit_51.
Axiom proof_of_split_words_safety_wit_52 : split_words_safety_wit_52.
Axiom proof_of_split_words_safety_wit_53 : split_words_safety_wit_53.
Axiom proof_of_split_words_safety_wit_54 : split_words_safety_wit_54.
Axiom proof_of_split_words_safety_wit_55 : split_words_safety_wit_55.
Axiom proof_of_split_words_safety_wit_56 : split_words_safety_wit_56.
Axiom proof_of_split_words_safety_wit_57 : split_words_safety_wit_57.
Axiom proof_of_split_words_safety_wit_58 : split_words_safety_wit_58.
Axiom proof_of_split_words_safety_wit_59 : split_words_safety_wit_59.
Axiom proof_of_split_words_safety_wit_60 : split_words_safety_wit_60.
Axiom proof_of_split_words_safety_wit_61 : split_words_safety_wit_61.
Axiom proof_of_split_words_safety_wit_62 : split_words_safety_wit_62.
Axiom proof_of_split_words_safety_wit_63 : split_words_safety_wit_63.
Axiom proof_of_split_words_safety_wit_64 : split_words_safety_wit_64.
Axiom proof_of_split_words_safety_wit_65 : split_words_safety_wit_65.
Axiom proof_of_split_words_safety_wit_66 : split_words_safety_wit_66.
Axiom proof_of_split_words_safety_wit_67 : split_words_safety_wit_67.
Axiom proof_of_split_words_safety_wit_68 : split_words_safety_wit_68.
Axiom proof_of_split_words_safety_wit_69 : split_words_safety_wit_69.
Axiom proof_of_split_words_safety_wit_70 : split_words_safety_wit_70.
Axiom proof_of_split_words_safety_wit_71 : split_words_safety_wit_71.
Axiom proof_of_split_words_safety_wit_72 : split_words_safety_wit_72.
Axiom proof_of_split_words_safety_wit_73 : split_words_safety_wit_73.
Axiom proof_of_split_words_safety_wit_74 : split_words_safety_wit_74.
Axiom proof_of_split_words_safety_wit_75 : split_words_safety_wit_75.
Axiom proof_of_split_words_safety_wit_76 : split_words_safety_wit_76.
Axiom proof_of_split_words_safety_wit_77 : split_words_safety_wit_77.
Axiom proof_of_split_words_safety_wit_78 : split_words_safety_wit_78.
Axiom proof_of_split_words_safety_wit_79 : split_words_safety_wit_79.
Axiom proof_of_split_words_safety_wit_80 : split_words_safety_wit_80.
Axiom proof_of_split_words_safety_wit_81 : split_words_safety_wit_81.
Axiom proof_of_split_words_safety_wit_82 : split_words_safety_wit_82.
Axiom proof_of_split_words_safety_wit_83 : split_words_safety_wit_83.
Axiom proof_of_split_words_safety_wit_84 : split_words_safety_wit_84.
Axiom proof_of_split_words_safety_wit_85 : split_words_safety_wit_85.
Axiom proof_of_split_words_safety_wit_86 : split_words_safety_wit_86.
Axiom proof_of_split_words_safety_wit_87 : split_words_safety_wit_87.
Axiom proof_of_split_words_safety_wit_88 : split_words_safety_wit_88.
Axiom proof_of_split_words_safety_wit_89 : split_words_safety_wit_89.
Axiom proof_of_split_words_safety_wit_90 : split_words_safety_wit_90.
Axiom proof_of_split_words_safety_wit_91 : split_words_safety_wit_91.
Axiom proof_of_split_words_safety_wit_92 : split_words_safety_wit_92.
Axiom proof_of_split_words_safety_wit_93 : split_words_safety_wit_93.
Axiom proof_of_split_words_safety_wit_94 : split_words_safety_wit_94.
Axiom proof_of_split_words_safety_wit_95 : split_words_safety_wit_95.
Axiom proof_of_split_words_safety_wit_96 : split_words_safety_wit_96.
Axiom proof_of_split_words_safety_wit_97 : split_words_safety_wit_97.
Axiom proof_of_split_words_safety_wit_98 : split_words_safety_wit_98.
Axiom proof_of_split_words_safety_wit_99 : split_words_safety_wit_99.
Axiom proof_of_split_words_safety_wit_100 : split_words_safety_wit_100.
Axiom proof_of_split_words_safety_wit_101 : split_words_safety_wit_101.
Axiom proof_of_split_words_safety_wit_102 : split_words_safety_wit_102.
Axiom proof_of_split_words_safety_wit_103 : split_words_safety_wit_103.
Axiom proof_of_split_words_safety_wit_104 : split_words_safety_wit_104.
Axiom proof_of_split_words_safety_wit_105 : split_words_safety_wit_105.
Axiom proof_of_split_words_safety_wit_106 : split_words_safety_wit_106.
Axiom proof_of_split_words_safety_wit_107 : split_words_safety_wit_107.
Axiom proof_of_split_words_safety_wit_108 : split_words_safety_wit_108.
Axiom proof_of_split_words_safety_wit_109 : split_words_safety_wit_109.
Axiom proof_of_split_words_safety_wit_110 : split_words_safety_wit_110.
Axiom proof_of_split_words_safety_wit_111 : split_words_safety_wit_111.
Axiom proof_of_split_words_safety_wit_112 : split_words_safety_wit_112.
Axiom proof_of_split_words_safety_wit_113 : split_words_safety_wit_113.
Axiom proof_of_split_words_safety_wit_114 : split_words_safety_wit_114.
Axiom proof_of_split_words_safety_wit_115 : split_words_safety_wit_115.
Axiom proof_of_split_words_safety_wit_116 : split_words_safety_wit_116.
Axiom proof_of_split_words_safety_wit_117 : split_words_safety_wit_117.
Axiom proof_of_split_words_safety_wit_118 : split_words_safety_wit_118.
Axiom proof_of_split_words_entail_wit_1_1 : split_words_entail_wit_1_1.
Axiom proof_of_split_words_entail_wit_1_2 : split_words_entail_wit_1_2.
Axiom proof_of_split_words_entail_wit_2_1 : split_words_entail_wit_2_1.
Axiom proof_of_split_words_entail_wit_2_2 : split_words_entail_wit_2_2.
Axiom proof_of_split_words_entail_wit_3_1 : split_words_entail_wit_3_1.
Axiom proof_of_split_words_entail_wit_3_2 : split_words_entail_wit_3_2.
Axiom proof_of_split_words_entail_wit_4_1 : split_words_entail_wit_4_1.
Axiom proof_of_split_words_entail_wit_4_2 : split_words_entail_wit_4_2.
Axiom proof_of_split_words_entail_wit_5_1 : split_words_entail_wit_5_1.
Axiom proof_of_split_words_entail_wit_5_2 : split_words_entail_wit_5_2.
Axiom proof_of_split_words_entail_wit_6_1 : split_words_entail_wit_6_1.
Axiom proof_of_split_words_entail_wit_6_2 : split_words_entail_wit_6_2.
Axiom proof_of_split_words_entail_wit_7_1 : split_words_entail_wit_7_1.
Axiom proof_of_split_words_entail_wit_7_2 : split_words_entail_wit_7_2.
Axiom proof_of_split_words_entail_wit_7_3 : split_words_entail_wit_7_3.
Axiom proof_of_split_words_entail_wit_7_4 : split_words_entail_wit_7_4.
Axiom proof_of_split_words_entail_wit_8_1 : split_words_entail_wit_8_1.
Axiom proof_of_split_words_entail_wit_8_2 : split_words_entail_wit_8_2.
Axiom proof_of_split_words_entail_wit_8_3 : split_words_entail_wit_8_3.
Axiom proof_of_split_words_entail_wit_8_4 : split_words_entail_wit_8_4.
Axiom proof_of_split_words_entail_wit_8_5 : split_words_entail_wit_8_5.
Axiom proof_of_split_words_entail_wit_8_6 : split_words_entail_wit_8_6.
Axiom proof_of_split_words_entail_wit_8_7 : split_words_entail_wit_8_7.
Axiom proof_of_split_words_entail_wit_8_8 : split_words_entail_wit_8_8.
Axiom proof_of_split_words_entail_wit_8_9 : split_words_entail_wit_8_9.
Axiom proof_of_split_words_entail_wit_8_10 : split_words_entail_wit_8_10.
Axiom proof_of_split_words_entail_wit_8_11 : split_words_entail_wit_8_11.
Axiom proof_of_split_words_entail_wit_8_12 : split_words_entail_wit_8_12.
Axiom proof_of_split_words_entail_wit_9_1 : split_words_entail_wit_9_1.
Axiom proof_of_split_words_entail_wit_9_2 : split_words_entail_wit_9_2.
Axiom proof_of_split_words_entail_wit_10_1 : split_words_entail_wit_10_1.
Axiom proof_of_split_words_entail_wit_10_2 : split_words_entail_wit_10_2.
Axiom proof_of_split_words_entail_wit_11_1 : split_words_entail_wit_11_1.
Axiom proof_of_split_words_entail_wit_11_2 : split_words_entail_wit_11_2.
Axiom proof_of_split_words_entail_wit_11_3 : split_words_entail_wit_11_3.
Axiom proof_of_split_words_entail_wit_11_4 : split_words_entail_wit_11_4.
Axiom proof_of_split_words_entail_wit_12 : split_words_entail_wit_12.
Axiom proof_of_split_words_entail_wit_13_1 : split_words_entail_wit_13_1.
Axiom proof_of_split_words_entail_wit_13_2 : split_words_entail_wit_13_2.
Axiom proof_of_split_words_entail_wit_13_3 : split_words_entail_wit_13_3.
Axiom proof_of_split_words_entail_wit_13_4 : split_words_entail_wit_13_4.
Axiom proof_of_split_words_entail_wit_14 : split_words_entail_wit_14.
Axiom proof_of_split_words_return_wit_1 : split_words_return_wit_1.
Axiom proof_of_split_words_return_wit_2 : split_words_return_wit_2.
Axiom proof_of_split_words_return_wit_3 : split_words_return_wit_3.
Axiom proof_of_split_words_return_wit_4 : split_words_return_wit_4.
Axiom proof_of_split_words_return_wit_5 : split_words_return_wit_5.
Axiom proof_of_split_words_partial_solve_wit_1_pure : split_words_partial_solve_wit_1_pure.
Axiom proof_of_split_words_partial_solve_wit_1 : split_words_partial_solve_wit_1.
Axiom proof_of_split_words_partial_solve_wit_2_pure : split_words_partial_solve_wit_2_pure.
Axiom proof_of_split_words_partial_solve_wit_2 : split_words_partial_solve_wit_2.
Axiom proof_of_split_words_partial_solve_wit_3_pure : split_words_partial_solve_wit_3_pure.
Axiom proof_of_split_words_partial_solve_wit_3 : split_words_partial_solve_wit_3.
Axiom proof_of_split_words_partial_solve_wit_4 : split_words_partial_solve_wit_4.
Axiom proof_of_split_words_partial_solve_wit_5_pure : split_words_partial_solve_wit_5_pure.
Axiom proof_of_split_words_partial_solve_wit_5 : split_words_partial_solve_wit_5.
Axiom proof_of_split_words_partial_solve_wit_6 : split_words_partial_solve_wit_6.
Axiom proof_of_split_words_partial_solve_wit_7 : split_words_partial_solve_wit_7.
Axiom proof_of_split_words_partial_solve_wit_8 : split_words_partial_solve_wit_8.
Axiom proof_of_split_words_partial_solve_wit_9 : split_words_partial_solve_wit_9.
Axiom proof_of_split_words_partial_solve_wit_10 : split_words_partial_solve_wit_10.
Axiom proof_of_split_words_partial_solve_wit_11 : split_words_partial_solve_wit_11.
Axiom proof_of_split_words_partial_solve_wit_12 : split_words_partial_solve_wit_12.
Axiom proof_of_split_words_partial_solve_wit_13 : split_words_partial_solve_wit_13.
Axiom proof_of_split_words_partial_solve_wit_14 : split_words_partial_solve_wit_14.
Axiom proof_of_split_words_partial_solve_wit_15 : split_words_partial_solve_wit_15.
Axiom proof_of_split_words_partial_solve_wit_16 : split_words_partial_solve_wit_16.
Axiom proof_of_split_words_partial_solve_wit_17 : split_words_partial_solve_wit_17.
Axiom proof_of_split_words_partial_solve_wit_18 : split_words_partial_solve_wit_18.
Axiom proof_of_split_words_partial_solve_wit_19 : split_words_partial_solve_wit_19.
Axiom proof_of_split_words_partial_solve_wit_20 : split_words_partial_solve_wit_20.
Axiom proof_of_split_words_partial_solve_wit_21 : split_words_partial_solve_wit_21.
Axiom proof_of_split_words_partial_solve_wit_22_pure : split_words_partial_solve_wit_22_pure.
Axiom proof_of_split_words_partial_solve_wit_22 : split_words_partial_solve_wit_22.
Axiom proof_of_split_words_partial_solve_wit_23 : split_words_partial_solve_wit_23.
Axiom proof_of_split_words_partial_solve_wit_24_pure : split_words_partial_solve_wit_24_pure.
Axiom proof_of_split_words_partial_solve_wit_24 : split_words_partial_solve_wit_24.
Axiom proof_of_split_words_partial_solve_wit_25 : split_words_partial_solve_wit_25.

End VC_Correct.
