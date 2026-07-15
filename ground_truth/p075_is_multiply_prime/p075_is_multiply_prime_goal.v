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
Require Import p075_is_multiply_prime.
Local Open Scope sac.

(*----- Function is_multiply_prime -----*)

Definition is_multiply_prime_safety_wit_1 := 
forall (a_pre: Z) (PreH1 : (problem_75_pre a_pre )) (PreH2 : (2 <= a_pre)) (PreH3 : (a_pre < 100)) ,
  ((( &( "num" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_multiply_prime_safety_wit_2 := 
forall (a_pre: Z) (PreH1 : (problem_75_pre a_pre )) (PreH2 : (2 <= a_pre)) (PreH3 : (a_pre < 100)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "num" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition is_multiply_prime_safety_wit_3 := 
forall (a_pre: Z) (num: Z) (a: Z) (i: Z) (PreH1 : (2 <= i)) (PreH2 : (i <= 10)) (PreH3 : (a >= 2)) (PreH4 : (a <= a_pre)) (PreH5 : (0 <= num)) (PreH6 : ((num + a ) <= a_pre)) (PreH7 : (mp_outer_inv a_pre i a num )) (PreH8 : (problem_75_pre a_pre )) (PreH9 : (2 <= a_pre)) (PreH10 : (a_pre < 100)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "num" ) )) # Int  |-> num)
|--
  “ ((i * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * i )) ”
.

Definition is_multiply_prime_safety_wit_4 := 
forall (a_pre: Z) (num: Z) (a_2: Z) (i_2: Z) (num_2: Z) (i: Z) (a: Z) (PreH1 : (a >= 2)) (PreH2 : (a <= a_pre)) (PreH3 : (i >= 2)) (PreH4 : (i <= 9)) (PreH5 : (0 <= num_2)) (PreH6 : ((num_2 + a ) <= a_pre)) (PreH7 : (mp_outer_inv a_pre i a num_2 )) (PreH8 : ((i_2 * i_2 ) <= a_2)) (PreH9 : (2 <= i_2)) (PreH10 : (i_2 <= 10)) (PreH11 : (a_2 >= 2)) (PreH12 : (a_2 <= a_pre)) (PreH13 : (0 <= num)) (PreH14 : ((num + a_2 ) <= a_pre)) (PreH15 : (mp_outer_inv a_pre i_2 a_2 num )) (PreH16 : (problem_75_pre a_pre )) (PreH17 : (2 <= a_pre)) (PreH18 : (a_pre < 100)) ,
  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_2)
|--
  “ ((a <> (INT_MIN)) \/ (i <> (-1))) ” 
  &&  “ (i <> 0) ”
.

Definition is_multiply_prime_safety_wit_5 := 
forall (a_pre: Z) (num: Z) (a: Z) (i: Z) (num_2: Z) (i_2: Z) (a_2: Z) (PreH1 : (a_2 >= 2)) (PreH2 : (a_2 <= a_pre)) (PreH3 : (i_2 >= 2)) (PreH4 : (i_2 <= 9)) (PreH5 : (0 <= num_2)) (PreH6 : ((num_2 + a_2 ) <= a_pre)) (PreH7 : (mp_outer_inv a_pre i_2 a_2 num_2 )) (PreH8 : ((i * i ) <= a)) (PreH9 : (2 <= i)) (PreH10 : (i <= 10)) (PreH11 : (a >= 2)) (PreH12 : (a <= a_pre)) (PreH13 : (0 <= num)) (PreH14 : ((num + a ) <= a_pre)) (PreH15 : (mp_outer_inv a_pre i a num )) (PreH16 : (problem_75_pre a_pre )) (PreH17 : (2 <= a_pre)) (PreH18 : (a_pre < 100)) ,
  ((( &( "a" ) )) # Int  |-> a_2)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "num" ) )) # Int  |-> num_2)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_multiply_prime_safety_wit_6 := 
forall (a_pre: Z) (num: Z) (a_2: Z) (i_2: Z) (num_2: Z) (i: Z) (a: Z) (PreH1 : (a > i)) (PreH2 : ((a % ( i ) ) = 0)) (PreH3 : (a >= 2)) (PreH4 : (a <= a_pre)) (PreH5 : (i >= 2)) (PreH6 : (i <= 9)) (PreH7 : (0 <= num_2)) (PreH8 : ((num_2 + a ) <= a_pre)) (PreH9 : (mp_outer_inv a_pre i a num_2 )) (PreH10 : ((i_2 * i_2 ) <= a_2)) (PreH11 : (2 <= i_2)) (PreH12 : (i_2 <= 10)) (PreH13 : (a_2 >= 2)) (PreH14 : (a_2 <= a_pre)) (PreH15 : (0 <= num)) (PreH16 : ((num + a_2 ) <= a_pre)) (PreH17 : (mp_outer_inv a_pre i_2 a_2 num )) (PreH18 : (problem_75_pre a_pre )) (PreH19 : (2 <= a_pre)) (PreH20 : (a_pre < 100)) ,
  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_2)
|--
  “ ((a <> (INT_MIN)) \/ (i <> (-1))) ” 
  &&  “ (i <> 0) ”
.

Definition is_multiply_prime_safety_wit_7 := 
forall (a_pre: Z) (num_2: Z) (a: Z) (i: Z) (num: Z) (i_2: Z) (a_2: Z) (PreH1 : (a_2 > i_2)) (PreH2 : ((a_2 % ( i_2 ) ) = 0)) (PreH3 : (a_2 >= 2)) (PreH4 : (a_2 <= a_pre)) (PreH5 : (i_2 >= 2)) (PreH6 : (i_2 <= 9)) (PreH7 : (0 <= num)) (PreH8 : ((num + a_2 ) <= a_pre)) (PreH9 : (mp_outer_inv a_pre i_2 a_2 num )) (PreH10 : ((i * i ) <= a)) (PreH11 : (2 <= i)) (PreH12 : (i <= 10)) (PreH13 : (a >= 2)) (PreH14 : (a <= a_pre)) (PreH15 : (0 <= num_2)) (PreH16 : ((num_2 + a ) <= a_pre)) (PreH17 : (mp_outer_inv a_pre i a num_2 )) (PreH18 : (problem_75_pre a_pre )) (PreH19 : (2 <= a_pre)) (PreH20 : (a_pre < 100)) ,
  ((( &( "a" ) )) # Int  |-> (a_2 ÷ i_2 ))
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "num" ) )) # Int  |-> num)
|--
  “ ((num + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (num + 1 )) ”
.

Definition is_multiply_prime_safety_wit_8 := 
forall (a_pre: Z) (num: Z) (a: Z) (i: Z) (num_2: Z) (i_2: Z) (a_2: Z) (PreH1 : (a_2 > i_2)) (PreH2 : ((a_2 % ( i_2 ) ) = 0)) (PreH3 : (a_2 >= 2)) (PreH4 : (a_2 <= a_pre)) (PreH5 : (i_2 >= 2)) (PreH6 : (i_2 <= 9)) (PreH7 : (0 <= num_2)) (PreH8 : ((num_2 + a_2 ) <= a_pre)) (PreH9 : (mp_outer_inv a_pre i_2 a_2 num_2 )) (PreH10 : ((i * i ) <= a)) (PreH11 : (2 <= i)) (PreH12 : (i <= 10)) (PreH13 : (a >= 2)) (PreH14 : (a <= a_pre)) (PreH15 : (0 <= num)) (PreH16 : ((num + a ) <= a_pre)) (PreH17 : (mp_outer_inv a_pre i a num )) (PreH18 : (problem_75_pre a_pre )) (PreH19 : (2 <= a_pre)) (PreH20 : (a_pre < 100)) ,
  ((( &( "a" ) )) # Int  |-> (a_2 ÷ i_2 ))
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "num" ) )) # Int  |-> num_2)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_multiply_prime_safety_wit_9 := 
forall (a_pre: Z) (num: Z) (a: Z) (i_2: Z) (num_2: Z) (i: Z) (a_2: Z) (PreH1 : ((a_2 % ( i ) ) <> 0)) (PreH2 : (a_2 >= 2)) (PreH3 : (a_2 <= a_pre)) (PreH4 : (i >= 2)) (PreH5 : (i <= 9)) (PreH6 : (0 <= num_2)) (PreH7 : ((num_2 + a_2 ) <= a_pre)) (PreH8 : (mp_outer_inv a_pre i a_2 num_2 )) (PreH9 : ((i_2 * i_2 ) <= a)) (PreH10 : (2 <= i_2)) (PreH11 : (i_2 <= 10)) (PreH12 : (a >= 2)) (PreH13 : (a <= a_pre)) (PreH14 : (0 <= num)) (PreH15 : ((num + a ) <= a_pre)) (PreH16 : (mp_outer_inv a_pre i_2 a num )) (PreH17 : (problem_75_pre a_pre )) (PreH18 : (2 <= a_pre)) (PreH19 : (a_pre < 100)) ,
  ((( &( "a" ) )) # Int  |-> a_2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_2)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition is_multiply_prime_safety_wit_10 := 
forall (a_pre: Z) (num: Z) (a: Z) (i_2: Z) (num_2: Z) (i: Z) (a_2: Z) (PreH1 : (a_2 <= i)) (PreH2 : ((a_2 % ( i ) ) = 0)) (PreH3 : (a_2 >= 2)) (PreH4 : (a_2 <= a_pre)) (PreH5 : (i >= 2)) (PreH6 : (i <= 9)) (PreH7 : (0 <= num_2)) (PreH8 : ((num_2 + a_2 ) <= a_pre)) (PreH9 : (mp_outer_inv a_pre i a_2 num_2 )) (PreH10 : ((i_2 * i_2 ) <= a)) (PreH11 : (2 <= i_2)) (PreH12 : (i_2 <= 10)) (PreH13 : (a >= 2)) (PreH14 : (a <= a_pre)) (PreH15 : (0 <= num)) (PreH16 : ((num + a ) <= a_pre)) (PreH17 : (mp_outer_inv a_pre i_2 a num )) (PreH18 : (problem_75_pre a_pre )) (PreH19 : (2 <= a_pre)) (PreH20 : (a_pre < 100)) ,
  ((( &( "a" ) )) # Int  |-> a_2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_2)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition is_multiply_prime_safety_wit_11 := 
forall (a_pre: Z) (num: Z) (a: Z) (i: Z) (PreH1 : ((i * i ) > a)) (PreH2 : (2 <= i)) (PreH3 : (i <= 10)) (PreH4 : (a >= 2)) (PreH5 : (a <= a_pre)) (PreH6 : (0 <= num)) (PreH7 : ((num + a ) <= a_pre)) (PreH8 : (mp_outer_inv a_pre i a num )) (PreH9 : (problem_75_pre a_pre )) (PreH10 : (2 <= a_pre)) (PreH11 : (a_pre < 100)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "num" ) )) # Int  |-> num)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition is_multiply_prime_safety_wit_12 := 
forall (a_pre: Z) (num: Z) (a: Z) (i: Z) (PreH1 : (num = 2)) (PreH2 : ((i * i ) > a)) (PreH3 : (2 <= i)) (PreH4 : (i <= 10)) (PreH5 : (a >= 2)) (PreH6 : (a <= a_pre)) (PreH7 : (0 <= num)) (PreH8 : ((num + a ) <= a_pre)) (PreH9 : (mp_outer_inv a_pre i a num )) (PreH10 : (problem_75_pre a_pre )) (PreH11 : (2 <= a_pre)) (PreH12 : (a_pre < 100)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "num" ) )) # Int  |-> num)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_multiply_prime_safety_wit_13 := 
forall (a_pre: Z) (num: Z) (a: Z) (i: Z) (PreH1 : (num <> 2)) (PreH2 : ((i * i ) > a)) (PreH3 : (2 <= i)) (PreH4 : (i <= 10)) (PreH5 : (a >= 2)) (PreH6 : (a <= a_pre)) (PreH7 : (0 <= num)) (PreH8 : ((num + a ) <= a_pre)) (PreH9 : (mp_outer_inv a_pre i a num )) (PreH10 : (problem_75_pre a_pre )) (PreH11 : (2 <= a_pre)) (PreH12 : (a_pre < 100)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "num" ) )) # Int  |-> num)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_multiply_prime_entail_wit_1 := 
(
forall (a_pre: Z) (PreH1 : (problem_75_pre a_pre )) (PreH2 : (2 <= a_pre)) (PreH3 : (a_pre < 100)) ,
  TT && emp 
|--
  “ (2 <= 2) ” 
  &&  “ (2 <= 10) ” 
  &&  “ (a_pre >= 2) ” 
  &&  “ (a_pre <= a_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((0 + a_pre ) <= a_pre) ” 
  &&  “ (mp_outer_inv a_pre 2 a_pre 0 ) ” 
  &&  “ (problem_75_pre a_pre ) ” 
  &&  “ (2 <= a_pre) ” 
  &&  “ (a_pre < 100) ”
  &&  emp
) \/
(
forall (a_pre: Z) (PreH1 : (problem_75_pre a_pre )) (PreH2 : (2 <= a_pre)) (PreH3 : (a_pre < 100)) ,
  TT && emp 
|--
  “ (mp_outer_inv a_pre 2 a_pre 0 ) ”
  &&  emp
).

Definition is_multiply_prime_entail_wit_1_split_goal_1 := 
forall (a_pre: Z) (PreH1 : (problem_75_pre a_pre )) (PreH2 : (2 <= a_pre)) (PreH3 : (a_pre < 100)) ,
  (mp_outer_inv a_pre 2 a_pre 0 )
.

Definition is_multiply_prime_entail_wit_2 := 
forall (a_pre: Z) (num: Z) (a: Z) (i: Z) (PreH1 : ((i * i ) <= a)) (PreH2 : (2 <= i)) (PreH3 : (i <= 10)) (PreH4 : (a >= 2)) (PreH5 : (a <= a_pre)) (PreH6 : (0 <= num)) (PreH7 : ((num + a ) <= a_pre)) (PreH8 : (mp_outer_inv a_pre i a num )) (PreH9 : (problem_75_pre a_pre )) (PreH10 : (2 <= a_pre)) (PreH11 : (a_pre < 100)) ,
  TT && emp 
|--
  “ (a >= 2) ” 
  &&  “ (a <= a_pre) ” 
  &&  “ (i >= 2) ” 
  &&  “ (i <= 9) ” 
  &&  “ (0 <= num) ” 
  &&  “ ((num + a ) <= a_pre) ” 
  &&  “ (mp_outer_inv a_pre i a num ) ” 
  &&  “ ((i * i ) <= a) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= 10) ” 
  &&  “ (a >= 2) ” 
  &&  “ (a <= a_pre) ” 
  &&  “ (0 <= num) ” 
  &&  “ ((num + a ) <= a_pre) ” 
  &&  “ (mp_outer_inv a_pre i a num ) ” 
  &&  “ (problem_75_pre a_pre ) ” 
  &&  “ (2 <= a_pre) ” 
  &&  “ (a_pre < 100) ”
  &&  emp
.

Definition is_multiply_prime_entail_wit_3_1 := 
(
forall (a_pre: Z) (num_2: Z) (a_2: Z) (i_2: Z) (num: Z) (i: Z) (a: Z) (PreH1 : ((a % ( i ) ) <> 0)) (PreH2 : (a >= 2)) (PreH3 : (a <= a_pre)) (PreH4 : (i >= 2)) (PreH5 : (i <= 9)) (PreH6 : (0 <= num)) (PreH7 : ((num + a ) <= a_pre)) (PreH8 : (mp_outer_inv a_pre i a num )) (PreH9 : ((i_2 * i_2 ) <= a_2)) (PreH10 : (2 <= i_2)) (PreH11 : (i_2 <= 10)) (PreH12 : (a_2 >= 2)) (PreH13 : (a_2 <= a_pre)) (PreH14 : (0 <= num_2)) (PreH15 : ((num_2 + a_2 ) <= a_pre)) (PreH16 : (mp_outer_inv a_pre i_2 a_2 num_2 )) (PreH17 : (problem_75_pre a_pre )) (PreH18 : (2 <= a_pre)) (PreH19 : (a_pre < 100)) ,
  TT && emp 
|--
  “ (2 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 10) ” 
  &&  “ (a >= 2) ” 
  &&  “ (a <= a_pre) ” 
  &&  “ (0 <= num) ” 
  &&  “ ((num + a ) <= a_pre) ” 
  &&  “ (mp_outer_inv a_pre (i + 1 ) a num ) ” 
  &&  “ (problem_75_pre a_pre ) ” 
  &&  “ (2 <= a_pre) ” 
  &&  “ (a_pre < 100) ”
  &&  emp
) \/
(
forall (a_pre: Z) (num_2: Z) (a_2: Z) (i_2: Z) (num: Z) (i: Z) (a: Z) (PreH1 : ((a % ( i ) ) <> 0)) (PreH2 : (a >= 2)) (PreH3 : (a <= a_pre)) (PreH4 : (i >= 2)) (PreH5 : (i <= 9)) (PreH6 : (0 <= num)) (PreH7 : ((num + a ) <= a_pre)) (PreH8 : (mp_outer_inv a_pre i a num )) (PreH9 : ((i_2 * i_2 ) <= a_2)) (PreH10 : (2 <= i_2)) (PreH11 : (i_2 <= 10)) (PreH12 : (a_2 >= 2)) (PreH13 : (a_2 <= a_pre)) (PreH14 : (0 <= num_2)) (PreH15 : ((num_2 + a_2 ) <= a_pre)) (PreH16 : (mp_outer_inv a_pre i_2 a_2 num_2 )) (PreH17 : (problem_75_pre a_pre )) (PreH18 : (2 <= a_pre)) (PreH19 : (a_pre < 100)) ,
  TT && emp 
|--
  “ (mp_outer_inv a_pre (i + 1 ) a num ) ”
  &&  emp
).

Definition is_multiply_prime_entail_wit_3_1_split_goal_1 := 
forall (a_pre: Z) (num_2: Z) (a_2: Z) (i_2: Z) (num: Z) (i: Z) (a: Z) (PreH1 : ((a % ( i ) ) <> 0)) (PreH2 : (a >= 2)) (PreH3 : (a <= a_pre)) (PreH4 : (i >= 2)) (PreH5 : (i <= 9)) (PreH6 : (0 <= num)) (PreH7 : ((num + a ) <= a_pre)) (PreH8 : (mp_outer_inv a_pre i a num )) (PreH9 : ((i_2 * i_2 ) <= a_2)) (PreH10 : (2 <= i_2)) (PreH11 : (i_2 <= 10)) (PreH12 : (a_2 >= 2)) (PreH13 : (a_2 <= a_pre)) (PreH14 : (0 <= num_2)) (PreH15 : ((num_2 + a_2 ) <= a_pre)) (PreH16 : (mp_outer_inv a_pre i_2 a_2 num_2 )) (PreH17 : (problem_75_pre a_pre )) (PreH18 : (2 <= a_pre)) (PreH19 : (a_pre < 100)) ,
  (mp_outer_inv a_pre (i + 1 ) a num )
.

Definition is_multiply_prime_entail_wit_3_2 := 
(
forall (a_pre: Z) (num_2: Z) (a_2: Z) (i_2: Z) (num: Z) (i: Z) (a: Z) (PreH1 : (a <= i)) (PreH2 : ((a % ( i ) ) = 0)) (PreH3 : (a >= 2)) (PreH4 : (a <= a_pre)) (PreH5 : (i >= 2)) (PreH6 : (i <= 9)) (PreH7 : (0 <= num)) (PreH8 : ((num + a ) <= a_pre)) (PreH9 : (mp_outer_inv a_pre i a num )) (PreH10 : ((i_2 * i_2 ) <= a_2)) (PreH11 : (2 <= i_2)) (PreH12 : (i_2 <= 10)) (PreH13 : (a_2 >= 2)) (PreH14 : (a_2 <= a_pre)) (PreH15 : (0 <= num_2)) (PreH16 : ((num_2 + a_2 ) <= a_pre)) (PreH17 : (mp_outer_inv a_pre i_2 a_2 num_2 )) (PreH18 : (problem_75_pre a_pre )) (PreH19 : (2 <= a_pre)) (PreH20 : (a_pre < 100)) ,
  TT && emp 
|--
  “ (2 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 10) ” 
  &&  “ (a >= 2) ” 
  &&  “ (a <= a_pre) ” 
  &&  “ (0 <= num) ” 
  &&  “ ((num + a ) <= a_pre) ” 
  &&  “ (mp_outer_inv a_pre (i + 1 ) a num ) ” 
  &&  “ (problem_75_pre a_pre ) ” 
  &&  “ (2 <= a_pre) ” 
  &&  “ (a_pre < 100) ”
  &&  emp
) \/
(
forall (a_pre: Z) (num_2: Z) (a_2: Z) (i_2: Z) (num: Z) (i: Z) (a: Z) (PreH1 : (a <= i)) (PreH2 : ((a % ( i ) ) = 0)) (PreH3 : (a >= 2)) (PreH4 : (a <= a_pre)) (PreH5 : (i >= 2)) (PreH6 : (i <= 9)) (PreH7 : (0 <= num)) (PreH8 : ((num + a ) <= a_pre)) (PreH9 : (mp_outer_inv a_pre i a num )) (PreH10 : ((i_2 * i_2 ) <= a_2)) (PreH11 : (2 <= i_2)) (PreH12 : (i_2 <= 10)) (PreH13 : (a_2 >= 2)) (PreH14 : (a_2 <= a_pre)) (PreH15 : (0 <= num_2)) (PreH16 : ((num_2 + a_2 ) <= a_pre)) (PreH17 : (mp_outer_inv a_pre i_2 a_2 num_2 )) (PreH18 : (problem_75_pre a_pre )) (PreH19 : (2 <= a_pre)) (PreH20 : (a_pre < 100)) ,
  TT && emp 
|--
  “ (mp_outer_inv a_pre (i + 1 ) a num ) ”
  &&  emp
).

Definition is_multiply_prime_entail_wit_3_2_split_goal_1 := 
forall (a_pre: Z) (num_2: Z) (a_2: Z) (i_2: Z) (num: Z) (i: Z) (a: Z) (PreH1 : (a <= i)) (PreH2 : ((a % ( i ) ) = 0)) (PreH3 : (a >= 2)) (PreH4 : (a <= a_pre)) (PreH5 : (i >= 2)) (PreH6 : (i <= 9)) (PreH7 : (0 <= num)) (PreH8 : ((num + a ) <= a_pre)) (PreH9 : (mp_outer_inv a_pre i a num )) (PreH10 : ((i_2 * i_2 ) <= a_2)) (PreH11 : (2 <= i_2)) (PreH12 : (i_2 <= 10)) (PreH13 : (a_2 >= 2)) (PreH14 : (a_2 <= a_pre)) (PreH15 : (0 <= num_2)) (PreH16 : ((num_2 + a_2 ) <= a_pre)) (PreH17 : (mp_outer_inv a_pre i_2 a_2 num_2 )) (PreH18 : (problem_75_pre a_pre )) (PreH19 : (2 <= a_pre)) (PreH20 : (a_pre < 100)) ,
  (mp_outer_inv a_pre (i + 1 ) a num )
.

Definition is_multiply_prime_entail_wit_4 := 
(
forall (a_pre: Z) (num: Z) (a: Z) (i: Z) (num_2: Z) (i_2: Z) (a_2: Z) (PreH1 : (a_2 > i_2)) (PreH2 : ((a_2 % ( i_2 ) ) = 0)) (PreH3 : (a_2 >= 2)) (PreH4 : (a_2 <= a_pre)) (PreH5 : (i_2 >= 2)) (PreH6 : (i_2 <= 9)) (PreH7 : (0 <= num_2)) (PreH8 : ((num_2 + a_2 ) <= a_pre)) (PreH9 : (mp_outer_inv a_pre i_2 a_2 num_2 )) (PreH10 : ((i * i ) <= a)) (PreH11 : (2 <= i)) (PreH12 : (i <= 10)) (PreH13 : (a >= 2)) (PreH14 : (a <= a_pre)) (PreH15 : (0 <= num)) (PreH16 : ((num + a ) <= a_pre)) (PreH17 : (mp_outer_inv a_pre i a num )) (PreH18 : (problem_75_pre a_pre )) (PreH19 : (2 <= a_pre)) (PreH20 : (a_pre < 100)) ,
  TT && emp 
|--
  “ ((a_2 ÷ i_2 ) >= 2) ” 
  &&  “ ((a_2 ÷ i_2 ) <= a_pre) ” 
  &&  “ (i_2 >= 2) ” 
  &&  “ (i_2 <= 9) ” 
  &&  “ (0 <= (num_2 + 1 )) ” 
  &&  “ (((num_2 + 1 ) + (a_2 ÷ i_2 ) ) <= a_pre) ” 
  &&  “ (mp_outer_inv a_pre i_2 (a_2 ÷ i_2 ) (num_2 + 1 ) ) ” 
  &&  “ ((i * i ) <= a) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= 10) ” 
  &&  “ (a >= 2) ” 
  &&  “ (a <= a_pre) ” 
  &&  “ (0 <= num) ” 
  &&  “ ((num + a ) <= a_pre) ” 
  &&  “ (mp_outer_inv a_pre i a num ) ” 
  &&  “ (problem_75_pre a_pre ) ” 
  &&  “ (2 <= a_pre) ” 
  &&  “ (a_pre < 100) ”
  &&  emp
) \/
(
forall (a_pre: Z) (num: Z) (a: Z) (i: Z) (num_2: Z) (i_2: Z) (a_2: Z) (PreH1 : (a_2 > i_2)) (PreH2 : ((a_2 % ( i_2 ) ) = 0)) (PreH3 : (a_2 >= 2)) (PreH4 : (a_2 <= a_pre)) (PreH5 : (i_2 >= 2)) (PreH6 : (i_2 <= 9)) (PreH7 : (0 <= num_2)) (PreH8 : ((num_2 + a_2 ) <= a_pre)) (PreH9 : (mp_outer_inv a_pre i_2 a_2 num_2 )) (PreH10 : ((i * i ) <= a)) (PreH11 : (2 <= i)) (PreH12 : (i <= 10)) (PreH13 : (a >= 2)) (PreH14 : (a <= a_pre)) (PreH15 : (0 <= num)) (PreH16 : ((num + a ) <= a_pre)) (PreH17 : (mp_outer_inv a_pre i a num )) (PreH18 : (problem_75_pre a_pre )) (PreH19 : (2 <= a_pre)) (PreH20 : (a_pre < 100)) ,
  TT && emp 
|--
  “ (mp_outer_inv a_pre i_2 (a_2 ÷ i_2 ) (num_2 + 1 ) ) ” 
  &&  “ (((num_2 + 1 ) + (a_2 ÷ i_2 ) ) <= a_pre) ” 
  &&  “ ((a_2 ÷ i_2 ) <= a_pre) ” 
  &&  “ ((a_2 ÷ i_2 ) >= 2) ”
  &&  emp
).

Definition is_multiply_prime_entail_wit_4_split_goal_1 := 
forall (a_pre: Z) (num: Z) (a: Z) (i: Z) (num_2: Z) (i_2: Z) (a_2: Z) (PreH1 : (a_2 > i_2)) (PreH2 : ((a_2 % ( i_2 ) ) = 0)) (PreH3 : (a_2 >= 2)) (PreH4 : (a_2 <= a_pre)) (PreH5 : (i_2 >= 2)) (PreH6 : (i_2 <= 9)) (PreH7 : (0 <= num_2)) (PreH8 : ((num_2 + a_2 ) <= a_pre)) (PreH9 : (mp_outer_inv a_pre i_2 a_2 num_2 )) (PreH10 : ((i * i ) <= a)) (PreH11 : (2 <= i)) (PreH12 : (i <= 10)) (PreH13 : (a >= 2)) (PreH14 : (a <= a_pre)) (PreH15 : (0 <= num)) (PreH16 : ((num + a ) <= a_pre)) (PreH17 : (mp_outer_inv a_pre i a num )) (PreH18 : (problem_75_pre a_pre )) (PreH19 : (2 <= a_pre)) (PreH20 : (a_pre < 100)) ,
  (mp_outer_inv a_pre i_2 (a_2 ÷ i_2 ) (num_2 + 1 ) )
.

Definition is_multiply_prime_entail_wit_4_split_goal_2 := 
forall (a_pre: Z) (num: Z) (a: Z) (i: Z) (num_2: Z) (i_2: Z) (a_2: Z) (PreH1 : (a_2 > i_2)) (PreH2 : ((a_2 % ( i_2 ) ) = 0)) (PreH3 : (a_2 >= 2)) (PreH4 : (a_2 <= a_pre)) (PreH5 : (i_2 >= 2)) (PreH6 : (i_2 <= 9)) (PreH7 : (0 <= num_2)) (PreH8 : ((num_2 + a_2 ) <= a_pre)) (PreH9 : (mp_outer_inv a_pre i_2 a_2 num_2 )) (PreH10 : ((i * i ) <= a)) (PreH11 : (2 <= i)) (PreH12 : (i <= 10)) (PreH13 : (a >= 2)) (PreH14 : (a <= a_pre)) (PreH15 : (0 <= num)) (PreH16 : ((num + a ) <= a_pre)) (PreH17 : (mp_outer_inv a_pre i a num )) (PreH18 : (problem_75_pre a_pre )) (PreH19 : (2 <= a_pre)) (PreH20 : (a_pre < 100)) ,
  (((num_2 + 1 ) + (a_2 ÷ i_2 ) ) <= a_pre)
.

Definition is_multiply_prime_entail_wit_4_split_goal_3 := 
forall (a_pre: Z) (num: Z) (a: Z) (i: Z) (num_2: Z) (i_2: Z) (a_2: Z) (PreH1 : (a_2 > i_2)) (PreH2 : ((a_2 % ( i_2 ) ) = 0)) (PreH3 : (a_2 >= 2)) (PreH4 : (a_2 <= a_pre)) (PreH5 : (i_2 >= 2)) (PreH6 : (i_2 <= 9)) (PreH7 : (0 <= num_2)) (PreH8 : ((num_2 + a_2 ) <= a_pre)) (PreH9 : (mp_outer_inv a_pre i_2 a_2 num_2 )) (PreH10 : ((i * i ) <= a)) (PreH11 : (2 <= i)) (PreH12 : (i <= 10)) (PreH13 : (a >= 2)) (PreH14 : (a <= a_pre)) (PreH15 : (0 <= num)) (PreH16 : ((num + a ) <= a_pre)) (PreH17 : (mp_outer_inv a_pre i a num )) (PreH18 : (problem_75_pre a_pre )) (PreH19 : (2 <= a_pre)) (PreH20 : (a_pre < 100)) ,
  ((a_2 ÷ i_2 ) <= a_pre)
.

Definition is_multiply_prime_entail_wit_4_split_goal_4 := 
forall (a_pre: Z) (num: Z) (a: Z) (i: Z) (num_2: Z) (i_2: Z) (a_2: Z) (PreH1 : (a_2 > i_2)) (PreH2 : ((a_2 % ( i_2 ) ) = 0)) (PreH3 : (a_2 >= 2)) (PreH4 : (a_2 <= a_pre)) (PreH5 : (i_2 >= 2)) (PreH6 : (i_2 <= 9)) (PreH7 : (0 <= num_2)) (PreH8 : ((num_2 + a_2 ) <= a_pre)) (PreH9 : (mp_outer_inv a_pre i_2 a_2 num_2 )) (PreH10 : ((i * i ) <= a)) (PreH11 : (2 <= i)) (PreH12 : (i <= 10)) (PreH13 : (a >= 2)) (PreH14 : (a <= a_pre)) (PreH15 : (0 <= num)) (PreH16 : ((num + a ) <= a_pre)) (PreH17 : (mp_outer_inv a_pre i a num )) (PreH18 : (problem_75_pre a_pre )) (PreH19 : (2 <= a_pre)) (PreH20 : (a_pre < 100)) ,
  ((a_2 ÷ i_2 ) >= 2)
.

Definition is_multiply_prime_return_wit_1 := 
(
forall (a_pre: Z) (num: Z) (a: Z) (i: Z) (PreH1 : (num <> 2)) (PreH2 : ((i * i ) > a)) (PreH3 : (2 <= i)) (PreH4 : (i <= 10)) (PreH5 : (a >= 2)) (PreH6 : (a <= a_pre)) (PreH7 : (0 <= num)) (PreH8 : ((num + a ) <= a_pre)) (PreH9 : (mp_outer_inv a_pre i a num )) (PreH10 : (problem_75_pre a_pre )) (PreH11 : (2 <= a_pre)) (PreH12 : (a_pre < 100)) ,
  TT && emp 
|--
  “ (problem_75_spec_z a_pre 0 ) ”
  &&  emp
) \/
(
forall (a_pre: Z) (num: Z) (a: Z) (i: Z) (PreH1 : (num <> 2)) (PreH2 : ((i * i ) > a)) (PreH3 : (2 <= i)) (PreH4 : (i <= 10)) (PreH5 : (a >= 2)) (PreH6 : (a <= a_pre)) (PreH7 : (0 <= num)) (PreH8 : ((num + a ) <= a_pre)) (PreH9 : (mp_outer_inv a_pre i a num )) (PreH10 : (problem_75_pre a_pre )) (PreH11 : (2 <= a_pre)) (PreH12 : (a_pre < 100)) ,
  TT && emp 
|--
  “ (problem_75_spec_z a_pre 0 ) ”
  &&  emp
).

Definition is_multiply_prime_return_wit_1_split_goal_1 := 
forall (a_pre: Z) (num: Z) (a: Z) (i: Z) (PreH1 : (num <> 2)) (PreH2 : ((i * i ) > a)) (PreH3 : (2 <= i)) (PreH4 : (i <= 10)) (PreH5 : (a >= 2)) (PreH6 : (a <= a_pre)) (PreH7 : (0 <= num)) (PreH8 : ((num + a ) <= a_pre)) (PreH9 : (mp_outer_inv a_pre i a num )) (PreH10 : (problem_75_pre a_pre )) (PreH11 : (2 <= a_pre)) (PreH12 : (a_pre < 100)) ,
  (problem_75_spec_z a_pre 0 )
.

Definition is_multiply_prime_return_wit_2 := 
(
forall (a_pre: Z) (num: Z) (a: Z) (i: Z) (PreH1 : (num = 2)) (PreH2 : ((i * i ) > a)) (PreH3 : (2 <= i)) (PreH4 : (i <= 10)) (PreH5 : (a >= 2)) (PreH6 : (a <= a_pre)) (PreH7 : (0 <= num)) (PreH8 : ((num + a ) <= a_pre)) (PreH9 : (mp_outer_inv a_pre i a num )) (PreH10 : (problem_75_pre a_pre )) (PreH11 : (2 <= a_pre)) (PreH12 : (a_pre < 100)) ,
  TT && emp 
|--
  “ (problem_75_spec_z a_pre 1 ) ”
  &&  emp
) \/
(
forall (a_pre: Z) (num: Z) (a: Z) (i: Z) (PreH1 : (num = 2)) (PreH2 : ((i * i ) > a)) (PreH3 : (2 <= i)) (PreH4 : (i <= 10)) (PreH5 : (a >= 2)) (PreH6 : (a <= a_pre)) (PreH7 : (0 <= num)) (PreH8 : ((num + a ) <= a_pre)) (PreH9 : (mp_outer_inv a_pre i a num )) (PreH10 : (problem_75_pre a_pre )) (PreH11 : (2 <= a_pre)) (PreH12 : (a_pre < 100)) ,
  TT && emp 
|--
  “ (problem_75_spec_z a_pre 1 ) ”
  &&  emp
).

Definition is_multiply_prime_return_wit_2_split_goal_1 := 
forall (a_pre: Z) (num: Z) (a: Z) (i: Z) (PreH1 : (num = 2)) (PreH2 : ((i * i ) > a)) (PreH3 : (2 <= i)) (PreH4 : (i <= 10)) (PreH5 : (a >= 2)) (PreH6 : (a <= a_pre)) (PreH7 : (0 <= num)) (PreH8 : ((num + a ) <= a_pre)) (PreH9 : (mp_outer_inv a_pre i a num )) (PreH10 : (problem_75_pre a_pre )) (PreH11 : (2 <= a_pre)) (PreH12 : (a_pre < 100)) ,
  (problem_75_spec_z a_pre 1 )
.

Module Type VC_Correct.


Axiom proof_of_is_multiply_prime_safety_wit_1 : is_multiply_prime_safety_wit_1.
Axiom proof_of_is_multiply_prime_safety_wit_2 : is_multiply_prime_safety_wit_2.
Axiom proof_of_is_multiply_prime_safety_wit_3 : is_multiply_prime_safety_wit_3.
Axiom proof_of_is_multiply_prime_safety_wit_4 : is_multiply_prime_safety_wit_4.
Axiom proof_of_is_multiply_prime_safety_wit_5 : is_multiply_prime_safety_wit_5.
Axiom proof_of_is_multiply_prime_safety_wit_6 : is_multiply_prime_safety_wit_6.
Axiom proof_of_is_multiply_prime_safety_wit_7 : is_multiply_prime_safety_wit_7.
Axiom proof_of_is_multiply_prime_safety_wit_8 : is_multiply_prime_safety_wit_8.
Axiom proof_of_is_multiply_prime_safety_wit_9 : is_multiply_prime_safety_wit_9.
Axiom proof_of_is_multiply_prime_safety_wit_10 : is_multiply_prime_safety_wit_10.
Axiom proof_of_is_multiply_prime_safety_wit_11 : is_multiply_prime_safety_wit_11.
Axiom proof_of_is_multiply_prime_safety_wit_12 : is_multiply_prime_safety_wit_12.
Axiom proof_of_is_multiply_prime_safety_wit_13 : is_multiply_prime_safety_wit_13.
Axiom proof_of_is_multiply_prime_entail_wit_1 : is_multiply_prime_entail_wit_1.
Axiom proof_of_is_multiply_prime_entail_wit_2 : is_multiply_prime_entail_wit_2.
Axiom proof_of_is_multiply_prime_entail_wit_3_1 : is_multiply_prime_entail_wit_3_1.
Axiom proof_of_is_multiply_prime_entail_wit_3_2 : is_multiply_prime_entail_wit_3_2.
Axiom proof_of_is_multiply_prime_entail_wit_4 : is_multiply_prime_entail_wit_4.
Axiom proof_of_is_multiply_prime_return_wit_1 : is_multiply_prime_return_wit_1.
Axiom proof_of_is_multiply_prime_return_wit_2 : is_multiply_prime_return_wit_2.

End VC_Correct.
