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
Require Import p036_fizz_buzz.
Local Open Scope sac.

(*----- Function fizz_buzz -----*)

Definition fizz_buzz_safety_wit_1 :=
forall (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 46340)) ,
  ((( &( "count" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fizz_buzz_safety_wit_2 :=
forall (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 46340)) ,
  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fizz_buzz_safety_wit_3 :=
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (count = (fizzbuzz_upto (i)))) (PreH5 : (0 <= count)) (PreH6 : (count <= (i * i ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 46340)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((i <> (INT_MIN)) \/ (11 <> (-1))) ”
  &&  “ (11 <> 0) ”
.

Definition fizz_buzz_safety_wit_4 :=
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (count = (fizzbuzz_upto (i)))) (PreH5 : (0 <= count)) (PreH6 : (count <= (i * i ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 46340)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (11 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 11) ”
.

Definition fizz_buzz_safety_wit_5 :=
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (count = (fizzbuzz_upto (i)))) (PreH5 : (0 <= count)) (PreH6 : (count <= (i * i ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 46340)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fizz_buzz_safety_wit_6 :=
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (0 <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : (0 <= count_2)) (PreH5 : ((i_2 % ( 11 ) ) = 0)) (PreH6 : (0 <= q)) (PreH7 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH8 : ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH9 : ((i % ( 11 ) ) = 0)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (count = (fizzbuzz_upto (i)))) (PreH14 : (0 <= count)) (PreH15 : (count <= (i * i ))) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 46340)) ,
  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fizz_buzz_safety_wit_7 :=
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) (PreH1 : (q > 0)) (PreH2 : (i_2 < n_pre)) (PreH3 : (0 <= i_2)) (PreH4 : (i_2 <= n_pre)) (PreH5 : (0 <= count_2)) (PreH6 : ((i_2 % ( 11 ) ) = 0)) (PreH7 : (0 <= q)) (PreH8 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH9 : ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH10 : ((i % ( 11 ) ) = 0)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (count = (fizzbuzz_upto (i)))) (PreH15 : (0 <= count)) (PreH16 : (count <= (i * i ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 46340)) ,
  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((q <> (INT_MIN)) \/ (10 <> (-1))) ”
  &&  “ (10 <> 0) ”
.

Definition fizz_buzz_safety_wit_8 :=
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) (PreH1 : (q > 0)) (PreH2 : (i_2 < n_pre)) (PreH3 : (0 <= i_2)) (PreH4 : (i_2 <= n_pre)) (PreH5 : (0 <= count_2)) (PreH6 : ((i_2 % ( 11 ) ) = 0)) (PreH7 : (0 <= q)) (PreH8 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH9 : ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH10 : ((i % ( 11 ) ) = 0)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (count = (fizzbuzz_upto (i)))) (PreH15 : (0 <= count)) (PreH16 : (count <= (i * i ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 46340)) ,
  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (10 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 10) ”
.

Definition fizz_buzz_safety_wit_9 :=
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) (PreH1 : (q > 0)) (PreH2 : (i_2 < n_pre)) (PreH3 : (0 <= i_2)) (PreH4 : (i_2 <= n_pre)) (PreH5 : (0 <= count_2)) (PreH6 : ((i_2 % ( 11 ) ) = 0)) (PreH7 : (0 <= q)) (PreH8 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH9 : ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH10 : ((i % ( 11 ) ) = 0)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (count = (fizzbuzz_upto (i)))) (PreH15 : (0 <= count)) (PreH16 : (count <= (i * i ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 46340)) ,
  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (7 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 7) ”
.

Definition fizz_buzz_safety_wit_10 :=
(
forall (n_pre: Z) (count_2: Z) (i: Z) (q: Z) (count: Z) (i_2: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (i_2 < n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (0 <= count)) (PreH7 : ((i_2 % ( 11 ) ) = 0)) (PreH8 : (0 <= q)) (PreH9 : ((count + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH10 : ((count + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH11 : ((i % ( 11 ) ) = 0)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (count_2 = (fizzbuzz_upto (i)))) (PreH16 : (0 <= count_2)) (PreH17 : (count_2 <= (i * i ))) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 46340)) ,
  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((count + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (count + 1 )) ”
) \/
(
forall (n_pre: Z) (count_2: Z) (i: Z) (q: Z) (count: Z) (i_2: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (i_2 < n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (0 <= count)) (PreH7 : ((i_2 % ( 11 ) ) = 0)) (PreH8 : (0 <= q)) (PreH9 : ((count + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH10 : ((count + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH11 : ((i % ( 11 ) ) = 0)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (count_2 = (fizzbuzz_upto (i)))) (PreH16 : (0 <= count_2)) (PreH17 : (count_2 <= (i * i ))) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 46340)) ,
  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((count + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (count + 1 )) ”
).

Definition fizz_buzz_safety_wit_10_split_goal_1 :=
forall (n_pre: Z) (count_2: Z) (i: Z) (q: Z) (count: Z) (i_2: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (i_2 < n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (0 <= count)) (PreH7 : ((i_2 % ( 11 ) ) = 0)) (PreH8 : (0 <= q)) (PreH9 : ((count + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH10 : ((count + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH11 : ((i % ( 11 ) ) = 0)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (count_2 = (fizzbuzz_upto (i)))) (PreH16 : (0 <= count_2)) (PreH17 : (count_2 <= (i * i ))) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 46340)) ,
  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((count + 1 ) <= INT_MAX) ”
.

Definition fizz_buzz_safety_wit_10_split_goal_2 :=
forall (n_pre: Z) (count_2: Z) (i: Z) (q: Z) (count: Z) (i_2: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (i_2 < n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (0 <= count)) (PreH7 : ((i_2 % ( 11 ) ) = 0)) (PreH8 : (0 <= q)) (PreH9 : ((count + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH10 : ((count + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH11 : ((i % ( 11 ) ) = 0)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (count_2 = (fizzbuzz_upto (i)))) (PreH16 : (0 <= count_2)) (PreH17 : (count_2 <= (i * i ))) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 46340)) ,
  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition fizz_buzz_safety_wit_11 :=
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (i_2 < n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (0 <= count_2)) (PreH7 : ((i_2 % ( 11 ) ) = 0)) (PreH8 : (0 <= q)) (PreH9 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH10 : ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH11 : ((i % ( 11 ) ) = 0)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (count = (fizzbuzz_upto (i)))) (PreH16 : (0 <= count)) (PreH17 : (count <= (i * i ))) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 46340)) ,
  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fizz_buzz_safety_wit_12 :=
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (i_2 < n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (0 <= count_2)) (PreH7 : ((i_2 % ( 11 ) ) = 0)) (PreH8 : (0 <= q)) (PreH9 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH10 : ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH11 : ((i % ( 11 ) ) = 0)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (count = (fizzbuzz_upto (i)))) (PreH16 : (0 <= count)) (PreH17 : (count <= (i * i ))) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 46340)) ,
  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> (count_2 + 1 ))
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((q <> (INT_MIN)) \/ (10 <> (-1))) ”
  &&  “ (10 <> 0) ”
.

Definition fizz_buzz_safety_wit_13 :=
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (i_2 < n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (0 <= count_2)) (PreH7 : ((i_2 % ( 11 ) ) = 0)) (PreH8 : (0 <= q)) (PreH9 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH10 : ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH11 : ((i % ( 11 ) ) = 0)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (count = (fizzbuzz_upto (i)))) (PreH16 : (0 <= count)) (PreH17 : (count <= (i * i ))) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 46340)) ,
  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> (count_2 + 1 ))
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (10 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 10) ”
.

Definition fizz_buzz_safety_wit_14 :=
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) (PreH1 : ((q % ( 10 ) ) <> 7)) (PreH2 : (q > 0)) (PreH3 : (i_2 < n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (0 <= count_2)) (PreH7 : ((i_2 % ( 11 ) ) = 0)) (PreH8 : (0 <= q)) (PreH9 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH10 : ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH11 : ((i % ( 11 ) ) = 0)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (count = (fizzbuzz_upto (i)))) (PreH16 : (0 <= count)) (PreH17 : (count <= (i * i ))) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 46340)) ,
  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((q <> (INT_MIN)) \/ (10 <> (-1))) ”
  &&  “ (10 <> 0) ”
.

Definition fizz_buzz_safety_wit_15 :=
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) (PreH1 : ((q % ( 10 ) ) <> 7)) (PreH2 : (q > 0)) (PreH3 : (i_2 < n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (0 <= count_2)) (PreH7 : ((i_2 % ( 11 ) ) = 0)) (PreH8 : (0 <= q)) (PreH9 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH10 : ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH11 : ((i % ( 11 ) ) = 0)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (count = (fizzbuzz_upto (i)))) (PreH16 : (0 <= count)) (PreH17 : (count <= (i * i ))) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 46340)) ,
  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (10 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 10) ”
.

Definition fizz_buzz_safety_wit_16 :=
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : ((i % ( 11 ) ) <> 0)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (count = (fizzbuzz_upto (i)))) (PreH6 : (0 <= count)) (PreH7 : (count <= (i * i ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 46340)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((i <> (INT_MIN)) \/ (13 <> (-1))) ”
  &&  “ (13 <> 0) ”
.

Definition fizz_buzz_safety_wit_17 :=
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : ((i % ( 11 ) ) <> 0)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (count = (fizzbuzz_upto (i)))) (PreH6 : (0 <= count)) (PreH7 : (count <= (i * i ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 46340)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (13 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 13) ”
.

Definition fizz_buzz_safety_wit_18 :=
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : ((i % ( 11 ) ) <> 0)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (count = (fizzbuzz_upto (i)))) (PreH6 : (0 <= count)) (PreH7 : (count <= (i * i ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 46340)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fizz_buzz_safety_wit_19 :=
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (0 <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : (0 <= count_2)) (PreH5 : ((i_2 % ( 13 ) ) = 0)) (PreH6 : ((i_2 % ( 11 ) ) <> 0)) (PreH7 : (0 <= q)) (PreH8 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH9 : ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH10 : ((i % ( 13 ) ) = 0)) (PreH11 : ((i % ( 11 ) ) <> 0)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (count = (fizzbuzz_upto (i)))) (PreH16 : (0 <= count)) (PreH17 : (count <= (i * i ))) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 46340)) ,
  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fizz_buzz_safety_wit_20 :=
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) (PreH1 : (q > 0)) (PreH2 : (i_2 < n_pre)) (PreH3 : (0 <= i_2)) (PreH4 : (i_2 <= n_pre)) (PreH5 : (0 <= count_2)) (PreH6 : ((i_2 % ( 13 ) ) = 0)) (PreH7 : ((i_2 % ( 11 ) ) <> 0)) (PreH8 : (0 <= q)) (PreH9 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH10 : ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH11 : ((i % ( 13 ) ) = 0)) (PreH12 : ((i % ( 11 ) ) <> 0)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (count = (fizzbuzz_upto (i)))) (PreH17 : (0 <= count)) (PreH18 : (count <= (i * i ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 46340)) ,
  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((q <> (INT_MIN)) \/ (10 <> (-1))) ”
  &&  “ (10 <> 0) ”
.

Definition fizz_buzz_safety_wit_21 :=
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) (PreH1 : (q > 0)) (PreH2 : (i_2 < n_pre)) (PreH3 : (0 <= i_2)) (PreH4 : (i_2 <= n_pre)) (PreH5 : (0 <= count_2)) (PreH6 : ((i_2 % ( 13 ) ) = 0)) (PreH7 : ((i_2 % ( 11 ) ) <> 0)) (PreH8 : (0 <= q)) (PreH9 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH10 : ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH11 : ((i % ( 13 ) ) = 0)) (PreH12 : ((i % ( 11 ) ) <> 0)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (count = (fizzbuzz_upto (i)))) (PreH17 : (0 <= count)) (PreH18 : (count <= (i * i ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 46340)) ,
  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (10 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 10) ”
.

Definition fizz_buzz_safety_wit_22 :=
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) (PreH1 : (q > 0)) (PreH2 : (i_2 < n_pre)) (PreH3 : (0 <= i_2)) (PreH4 : (i_2 <= n_pre)) (PreH5 : (0 <= count_2)) (PreH6 : ((i_2 % ( 13 ) ) = 0)) (PreH7 : ((i_2 % ( 11 ) ) <> 0)) (PreH8 : (0 <= q)) (PreH9 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH10 : ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH11 : ((i % ( 13 ) ) = 0)) (PreH12 : ((i % ( 11 ) ) <> 0)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (count = (fizzbuzz_upto (i)))) (PreH17 : (0 <= count)) (PreH18 : (count <= (i * i ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 46340)) ,
  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (7 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 7) ”
.

Definition fizz_buzz_safety_wit_23 :=
(
forall (n_pre: Z) (count_2: Z) (i: Z) (q: Z) (count: Z) (i_2: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (i_2 < n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (0 <= count)) (PreH7 : ((i_2 % ( 13 ) ) = 0)) (PreH8 : ((i_2 % ( 11 ) ) <> 0)) (PreH9 : (0 <= q)) (PreH10 : ((count + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH11 : ((count + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH12 : ((i % ( 13 ) ) = 0)) (PreH13 : ((i % ( 11 ) ) <> 0)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (count_2 = (fizzbuzz_upto (i)))) (PreH18 : (0 <= count_2)) (PreH19 : (count_2 <= (i * i ))) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 46340)) ,
  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((count + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (count + 1 )) ”
) \/
(
forall (n_pre: Z) (count_2: Z) (i: Z) (q: Z) (count: Z) (i_2: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (i_2 < n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (0 <= count)) (PreH7 : ((i_2 % ( 13 ) ) = 0)) (PreH8 : ((i_2 % ( 11 ) ) <> 0)) (PreH9 : (0 <= q)) (PreH10 : ((count + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH11 : ((count + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH12 : ((i % ( 13 ) ) = 0)) (PreH13 : ((i % ( 11 ) ) <> 0)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (count_2 = (fizzbuzz_upto (i)))) (PreH18 : (0 <= count_2)) (PreH19 : (count_2 <= (i * i ))) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 46340)) ,
  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((count + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (count + 1 )) ”
).

Definition fizz_buzz_safety_wit_23_split_goal_1 :=
forall (n_pre: Z) (count_2: Z) (i: Z) (q: Z) (count: Z) (i_2: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (i_2 < n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (0 <= count)) (PreH7 : ((i_2 % ( 13 ) ) = 0)) (PreH8 : ((i_2 % ( 11 ) ) <> 0)) (PreH9 : (0 <= q)) (PreH10 : ((count + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH11 : ((count + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH12 : ((i % ( 13 ) ) = 0)) (PreH13 : ((i % ( 11 ) ) <> 0)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (count_2 = (fizzbuzz_upto (i)))) (PreH18 : (0 <= count_2)) (PreH19 : (count_2 <= (i * i ))) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 46340)) ,
  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((count + 1 ) <= INT_MAX) ”
.

Definition fizz_buzz_safety_wit_23_split_goal_2 :=
forall (n_pre: Z) (count_2: Z) (i: Z) (q: Z) (count: Z) (i_2: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (i_2 < n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (0 <= count)) (PreH7 : ((i_2 % ( 13 ) ) = 0)) (PreH8 : ((i_2 % ( 11 ) ) <> 0)) (PreH9 : (0 <= q)) (PreH10 : ((count + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH11 : ((count + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH12 : ((i % ( 13 ) ) = 0)) (PreH13 : ((i % ( 11 ) ) <> 0)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (count_2 = (fizzbuzz_upto (i)))) (PreH18 : (0 <= count_2)) (PreH19 : (count_2 <= (i * i ))) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 46340)) ,
  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition fizz_buzz_safety_wit_24 :=
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (i_2 < n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (0 <= count_2)) (PreH7 : ((i_2 % ( 13 ) ) = 0)) (PreH8 : ((i_2 % ( 11 ) ) <> 0)) (PreH9 : (0 <= q)) (PreH10 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH11 : ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH12 : ((i % ( 13 ) ) = 0)) (PreH13 : ((i % ( 11 ) ) <> 0)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (count = (fizzbuzz_upto (i)))) (PreH18 : (0 <= count)) (PreH19 : (count <= (i * i ))) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 46340)) ,
  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fizz_buzz_safety_wit_25 :=
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (i_2 < n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (0 <= count_2)) (PreH7 : ((i_2 % ( 13 ) ) = 0)) (PreH8 : ((i_2 % ( 11 ) ) <> 0)) (PreH9 : (0 <= q)) (PreH10 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH11 : ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH12 : ((i % ( 13 ) ) = 0)) (PreH13 : ((i % ( 11 ) ) <> 0)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (count = (fizzbuzz_upto (i)))) (PreH18 : (0 <= count)) (PreH19 : (count <= (i * i ))) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 46340)) ,
  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> (count_2 + 1 ))
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((q <> (INT_MIN)) \/ (10 <> (-1))) ”
  &&  “ (10 <> 0) ”
.

Definition fizz_buzz_safety_wit_26 :=
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (i_2 < n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (0 <= count_2)) (PreH7 : ((i_2 % ( 13 ) ) = 0)) (PreH8 : ((i_2 % ( 11 ) ) <> 0)) (PreH9 : (0 <= q)) (PreH10 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH11 : ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH12 : ((i % ( 13 ) ) = 0)) (PreH13 : ((i % ( 11 ) ) <> 0)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (count = (fizzbuzz_upto (i)))) (PreH18 : (0 <= count)) (PreH19 : (count <= (i * i ))) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 46340)) ,
  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> (count_2 + 1 ))
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (10 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 10) ”
.

Definition fizz_buzz_safety_wit_27 :=
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) (PreH1 : ((q % ( 10 ) ) <> 7)) (PreH2 : (q > 0)) (PreH3 : (i_2 < n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (0 <= count_2)) (PreH7 : ((i_2 % ( 13 ) ) = 0)) (PreH8 : ((i_2 % ( 11 ) ) <> 0)) (PreH9 : (0 <= q)) (PreH10 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH11 : ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH12 : ((i % ( 13 ) ) = 0)) (PreH13 : ((i % ( 11 ) ) <> 0)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (count = (fizzbuzz_upto (i)))) (PreH18 : (0 <= count)) (PreH19 : (count <= (i * i ))) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 46340)) ,
  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((q <> (INT_MIN)) \/ (10 <> (-1))) ”
  &&  “ (10 <> 0) ”
.

Definition fizz_buzz_safety_wit_28 :=
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) (PreH1 : ((q % ( 10 ) ) <> 7)) (PreH2 : (q > 0)) (PreH3 : (i_2 < n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (0 <= count_2)) (PreH7 : ((i_2 % ( 13 ) ) = 0)) (PreH8 : ((i_2 % ( 11 ) ) <> 0)) (PreH9 : (0 <= q)) (PreH10 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH11 : ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH12 : ((i % ( 13 ) ) = 0)) (PreH13 : ((i % ( 11 ) ) <> 0)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (count = (fizzbuzz_upto (i)))) (PreH18 : (0 <= count)) (PreH19 : (count <= (i * i ))) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 46340)) ,
  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (10 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 10) ”
.

Definition fizz_buzz_safety_wit_29 :=
forall (n_pre: Z) (count: Z) (i_2: Z) (q: Z) (count_2: Z) (i: Z) (PreH1 : (q <= 0)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= count_2)) (PreH6 : ((i % ( 11 ) ) = 0)) (PreH7 : (0 <= q)) (PreH8 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i)) + (count_digit7 (i)) ))) (PreH9 : ((count_2 + (count_digit7 (q)) ) <= (i * (i + 1 ) ))) (PreH10 : ((i_2 % ( 11 ) ) = 0)) (PreH11 : (i_2 < n_pre)) (PreH12 : (0 <= i_2)) (PreH13 : (i_2 <= n_pre)) (PreH14 : (count = (fizzbuzz_upto (i_2)))) (PreH15 : (0 <= count)) (PreH16 : (count <= (i_2 * i_2 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 46340)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition fizz_buzz_safety_wit_30 :=
forall (n_pre: Z) (count: Z) (i_2: Z) (q: Z) (count_2: Z) (i: Z) (PreH1 : (q <= 0)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= count_2)) (PreH6 : ((i % ( 13 ) ) = 0)) (PreH7 : ((i % ( 11 ) ) <> 0)) (PreH8 : (0 <= q)) (PreH9 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i)) + (count_digit7 (i)) ))) (PreH10 : ((count_2 + (count_digit7 (q)) ) <= (i * (i + 1 ) ))) (PreH11 : ((i_2 % ( 13 ) ) = 0)) (PreH12 : ((i_2 % ( 11 ) ) <> 0)) (PreH13 : (i_2 < n_pre)) (PreH14 : (0 <= i_2)) (PreH15 : (i_2 <= n_pre)) (PreH16 : (count = (fizzbuzz_upto (i_2)))) (PreH17 : (0 <= count)) (PreH18 : (count <= (i_2 * i_2 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 46340)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition fizz_buzz_safety_wit_31 :=
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : ((i % ( 13 ) ) <> 0)) (PreH2 : ((i % ( 11 ) ) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (count = (fizzbuzz_upto (i)))) (PreH7 : (0 <= count)) (PreH8 : (count <= (i * i ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 46340)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition fizz_buzz_entail_wit_1 :=
(
forall (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 46340)) ,
  TT && emp
|--
  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (0 = (fizzbuzz_upto (0))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (0 * 0 )) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 46340) ”
  &&  emp
) \/
(
forall (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 46340)) ,
  TT && emp
|--
  “ (0 = (fizzbuzz_upto (0))) ”
  &&  emp
).

Definition fizz_buzz_entail_wit_1_split_goal_1 :=
forall (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 46340)) ,
  TT && emp
|--
  “ (0 = (fizzbuzz_upto (0))) ”
.

Definition fizz_buzz_entail_wit_2 :=
(
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : ((i % ( 11 ) ) = 0)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (count = (fizzbuzz_upto (i)))) (PreH6 : (0 <= count)) (PreH7 : (count <= (i * i ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 46340)) ,
  TT && emp
|--
  “ (i < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= count) ”
  &&  “ ((i % ( 11 ) ) = 0) ”
  &&  “ (0 <= i) ”
  &&  “ ((count + (count_digit7 (i)) ) = ((fizzbuzz_upto (i)) + (count_digit7 (i)) )) ”
  &&  “ ((count + (count_digit7 (i)) ) <= (i * (i + 1 ) )) ”
  &&  “ ((i % ( 11 ) ) = 0) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (count = (fizzbuzz_upto (i))) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= (i * i )) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 46340) ”
  &&  emp
) \/
(
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : ((i % ( 11 ) ) = 0)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (count = (fizzbuzz_upto (i)))) (PreH6 : (0 <= count)) (PreH7 : (count <= (i * i ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 46340)) ,
  TT && emp
|--
  “ ((count + (count_digit7 (i)) ) <= (i * (i + 1 ) )) ”
  &&  emp
).

Definition fizz_buzz_entail_wit_2_split_goal_1 :=
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : ((i % ( 11 ) ) = 0)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (count = (fizzbuzz_upto (i)))) (PreH6 : (0 <= count)) (PreH7 : (count <= (i * i ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 46340)) ,
  TT && emp
|--
  “ ((count + (count_digit7 (i)) ) <= (i * (i + 1 ) )) ”
.

Definition fizz_buzz_entail_wit_3_1 :=
(
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (i_2 < n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (0 <= count_2)) (PreH7 : ((i_2 % ( 11 ) ) = 0)) (PreH8 : (0 <= q)) (PreH9 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH10 : ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH11 : ((i % ( 11 ) ) = 0)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (count = (fizzbuzz_upto (i)))) (PreH16 : (0 <= count)) (PreH17 : (count <= (i * i ))) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 46340)) ,
  TT && emp
|--
  “ (i_2 < n_pre) ”
  &&  “ (0 <= i_2) ”
  &&  “ (i_2 <= n_pre) ”
  &&  “ (0 <= (count_2 + 1 )) ”
  &&  “ ((i_2 % ( 11 ) ) = 0) ”
  &&  “ (0 <= (q ÷ 10 )) ”
  &&  “ (((count_2 + 1 ) + (count_digit7 ((q ÷ 10 ))) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) ”
  &&  “ (((count_2 + 1 ) + (count_digit7 ((q ÷ 10 ))) ) <= (i_2 * (i_2 + 1 ) )) ”
  &&  “ ((i % ( 11 ) ) = 0) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (count = (fizzbuzz_upto (i))) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= (i * i )) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 46340) ”
  &&  emp
) \/
(
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (i_2 < n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (0 <= count_2)) (PreH7 : ((i_2 % ( 11 ) ) = 0)) (PreH8 : (0 <= q)) (PreH9 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH10 : ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH11 : ((i % ( 11 ) ) = 0)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (count = (fizzbuzz_upto (i)))) (PreH16 : (0 <= count)) (PreH17 : (count <= (i * i ))) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 46340)) ,
  TT && emp
|--
  “ (((count_2 + 1 ) + (count_digit7 ((q ÷ 10 ))) ) <= (i_2 * (i_2 + 1 ) )) ”
  &&  “ (((count_2 + 1 ) + (count_digit7 ((q ÷ 10 ))) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) ”
  &&  “ (0 <= (q ÷ 10 )) ”
  &&  emp
).

Definition fizz_buzz_entail_wit_3_1_split_goal_1 :=
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (i_2 < n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (0 <= count_2)) (PreH7 : ((i_2 % ( 11 ) ) = 0)) (PreH8 : (0 <= q)) (PreH9 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH10 : ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH11 : ((i % ( 11 ) ) = 0)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (count = (fizzbuzz_upto (i)))) (PreH16 : (0 <= count)) (PreH17 : (count <= (i * i ))) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 46340)) ,
  TT && emp
|--
  “ (((count_2 + 1 ) + (count_digit7 ((q ÷ 10 ))) ) <= (i_2 * (i_2 + 1 ) )) ”
.

Definition fizz_buzz_entail_wit_3_1_split_goal_2 :=
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (i_2 < n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (0 <= count_2)) (PreH7 : ((i_2 % ( 11 ) ) = 0)) (PreH8 : (0 <= q)) (PreH9 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH10 : ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH11 : ((i % ( 11 ) ) = 0)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (count = (fizzbuzz_upto (i)))) (PreH16 : (0 <= count)) (PreH17 : (count <= (i * i ))) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 46340)) ,
  TT && emp
|--
  “ (((count_2 + 1 ) + (count_digit7 ((q ÷ 10 ))) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) ”
.

Definition fizz_buzz_entail_wit_3_1_split_goal_3 :=
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (i_2 < n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (0 <= count_2)) (PreH7 : ((i_2 % ( 11 ) ) = 0)) (PreH8 : (0 <= q)) (PreH9 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH10 : ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH11 : ((i % ( 11 ) ) = 0)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (count = (fizzbuzz_upto (i)))) (PreH16 : (0 <= count)) (PreH17 : (count <= (i * i ))) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 46340)) ,
  TT && emp
|--
  “ (0 <= (q ÷ 10 )) ”
.

Definition fizz_buzz_entail_wit_3_2 :=
(
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) (PreH1 : ((q % ( 10 ) ) <> 7)) (PreH2 : (q > 0)) (PreH3 : (i_2 < n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (0 <= count_2)) (PreH7 : ((i_2 % ( 11 ) ) = 0)) (PreH8 : (0 <= q)) (PreH9 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH10 : ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH11 : ((i % ( 11 ) ) = 0)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (count = (fizzbuzz_upto (i)))) (PreH16 : (0 <= count)) (PreH17 : (count <= (i * i ))) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 46340)) ,
  TT && emp
|--
  “ (i_2 < n_pre) ”
  &&  “ (0 <= i_2) ”
  &&  “ (i_2 <= n_pre) ”
  &&  “ (0 <= count_2) ”
  &&  “ ((i_2 % ( 11 ) ) = 0) ”
  &&  “ (0 <= (q ÷ 10 )) ”
  &&  “ ((count_2 + (count_digit7 ((q ÷ 10 ))) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) ”
  &&  “ ((count_2 + (count_digit7 ((q ÷ 10 ))) ) <= (i_2 * (i_2 + 1 ) )) ”
  &&  “ ((i % ( 11 ) ) = 0) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (count = (fizzbuzz_upto (i))) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= (i * i )) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 46340) ”
  &&  emp
) \/
(
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) (PreH1 : ((q % ( 10 ) ) <> 7)) (PreH2 : (q > 0)) (PreH3 : (i_2 < n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (0 <= count_2)) (PreH7 : ((i_2 % ( 11 ) ) = 0)) (PreH8 : (0 <= q)) (PreH9 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH10 : ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH11 : ((i % ( 11 ) ) = 0)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (count = (fizzbuzz_upto (i)))) (PreH16 : (0 <= count)) (PreH17 : (count <= (i * i ))) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 46340)) ,
  TT && emp
|--
  “ ((count_2 + (count_digit7 ((q ÷ 10 ))) ) <= (i_2 * (i_2 + 1 ) )) ”
  &&  “ ((count_2 + (count_digit7 ((q ÷ 10 ))) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) ”
  &&  “ (0 <= (q ÷ 10 )) ”
  &&  emp
).

Definition fizz_buzz_entail_wit_3_2_split_goal_1 :=
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) (PreH1 : ((q % ( 10 ) ) <> 7)) (PreH2 : (q > 0)) (PreH3 : (i_2 < n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (0 <= count_2)) (PreH7 : ((i_2 % ( 11 ) ) = 0)) (PreH8 : (0 <= q)) (PreH9 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH10 : ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH11 : ((i % ( 11 ) ) = 0)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (count = (fizzbuzz_upto (i)))) (PreH16 : (0 <= count)) (PreH17 : (count <= (i * i ))) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 46340)) ,
  TT && emp
|--
  “ ((count_2 + (count_digit7 ((q ÷ 10 ))) ) <= (i_2 * (i_2 + 1 ) )) ”
.

Definition fizz_buzz_entail_wit_3_2_split_goal_2 :=
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) (PreH1 : ((q % ( 10 ) ) <> 7)) (PreH2 : (q > 0)) (PreH3 : (i_2 < n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (0 <= count_2)) (PreH7 : ((i_2 % ( 11 ) ) = 0)) (PreH8 : (0 <= q)) (PreH9 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH10 : ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH11 : ((i % ( 11 ) ) = 0)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (count = (fizzbuzz_upto (i)))) (PreH16 : (0 <= count)) (PreH17 : (count <= (i * i ))) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 46340)) ,
  TT && emp
|--
  “ ((count_2 + (count_digit7 ((q ÷ 10 ))) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) ”
.

Definition fizz_buzz_entail_wit_3_2_split_goal_3 :=
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) (PreH1 : ((q % ( 10 ) ) <> 7)) (PreH2 : (q > 0)) (PreH3 : (i_2 < n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (0 <= count_2)) (PreH7 : ((i_2 % ( 11 ) ) = 0)) (PreH8 : (0 <= q)) (PreH9 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH10 : ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH11 : ((i % ( 11 ) ) = 0)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (count = (fizzbuzz_upto (i)))) (PreH16 : (0 <= count)) (PreH17 : (count <= (i * i ))) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 46340)) ,
  TT && emp
|--
  “ (0 <= (q ÷ 10 )) ”
.

Definition fizz_buzz_entail_wit_4 :=
(
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : ((i % ( 13 ) ) = 0)) (PreH2 : ((i % ( 11 ) ) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (count = (fizzbuzz_upto (i)))) (PreH7 : (0 <= count)) (PreH8 : (count <= (i * i ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 46340)) ,
  TT && emp
|--
  “ (i < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= count) ”
  &&  “ ((i % ( 13 ) ) = 0) ”
  &&  “ ((i % ( 11 ) ) <> 0) ”
  &&  “ (0 <= i) ”
  &&  “ ((count + (count_digit7 (i)) ) = ((fizzbuzz_upto (i)) + (count_digit7 (i)) )) ”
  &&  “ ((count + (count_digit7 (i)) ) <= (i * (i + 1 ) )) ”
  &&  “ ((i % ( 13 ) ) = 0) ”
  &&  “ ((i % ( 11 ) ) <> 0) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (count = (fizzbuzz_upto (i))) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= (i * i )) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 46340) ”
  &&  emp
) \/
(
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : ((i % ( 13 ) ) = 0)) (PreH2 : ((i % ( 11 ) ) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (count = (fizzbuzz_upto (i)))) (PreH7 : (0 <= count)) (PreH8 : (count <= (i * i ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 46340)) ,
  TT && emp
|--
  “ ((count + (count_digit7 (i)) ) <= (i * (i + 1 ) )) ”
  &&  emp
).

Definition fizz_buzz_entail_wit_4_split_goal_1 :=
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : ((i % ( 13 ) ) = 0)) (PreH2 : ((i % ( 11 ) ) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (count = (fizzbuzz_upto (i)))) (PreH7 : (0 <= count)) (PreH8 : (count <= (i * i ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 46340)) ,
  TT && emp
|--
  “ ((count + (count_digit7 (i)) ) <= (i * (i + 1 ) )) ”
.

Definition fizz_buzz_entail_wit_5_1 :=
(
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (i_2 < n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (0 <= count_2)) (PreH7 : ((i_2 % ( 13 ) ) = 0)) (PreH8 : ((i_2 % ( 11 ) ) <> 0)) (PreH9 : (0 <= q)) (PreH10 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH11 : ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH12 : ((i % ( 13 ) ) = 0)) (PreH13 : ((i % ( 11 ) ) <> 0)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (count = (fizzbuzz_upto (i)))) (PreH18 : (0 <= count)) (PreH19 : (count <= (i * i ))) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 46340)) ,
  TT && emp
|--
  “ (i_2 < n_pre) ”
  &&  “ (0 <= i_2) ”
  &&  “ (i_2 <= n_pre) ”
  &&  “ (0 <= (count_2 + 1 )) ”
  &&  “ ((i_2 % ( 13 ) ) = 0) ”
  &&  “ ((i_2 % ( 11 ) ) <> 0) ”
  &&  “ (0 <= (q ÷ 10 )) ”
  &&  “ (((count_2 + 1 ) + (count_digit7 ((q ÷ 10 ))) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) ”
  &&  “ (((count_2 + 1 ) + (count_digit7 ((q ÷ 10 ))) ) <= (i_2 * (i_2 + 1 ) )) ”
  &&  “ ((i % ( 13 ) ) = 0) ”
  &&  “ ((i % ( 11 ) ) <> 0) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (count = (fizzbuzz_upto (i))) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= (i * i )) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 46340) ”
  &&  emp
) \/
(
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (i_2 < n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (0 <= count_2)) (PreH7 : ((i_2 % ( 13 ) ) = 0)) (PreH8 : ((i_2 % ( 11 ) ) <> 0)) (PreH9 : (0 <= q)) (PreH10 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH11 : ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH12 : ((i % ( 13 ) ) = 0)) (PreH13 : ((i % ( 11 ) ) <> 0)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (count = (fizzbuzz_upto (i)))) (PreH18 : (0 <= count)) (PreH19 : (count <= (i * i ))) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 46340)) ,
  TT && emp
|--
  “ (((count_2 + 1 ) + (count_digit7 ((q ÷ 10 ))) ) <= (i_2 * (i_2 + 1 ) )) ”
  &&  “ (((count_2 + 1 ) + (count_digit7 ((q ÷ 10 ))) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) ”
  &&  “ (0 <= (q ÷ 10 )) ”
  &&  emp
).

Definition fizz_buzz_entail_wit_5_1_split_goal_1 :=
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (i_2 < n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (0 <= count_2)) (PreH7 : ((i_2 % ( 13 ) ) = 0)) (PreH8 : ((i_2 % ( 11 ) ) <> 0)) (PreH9 : (0 <= q)) (PreH10 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH11 : ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH12 : ((i % ( 13 ) ) = 0)) (PreH13 : ((i % ( 11 ) ) <> 0)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (count = (fizzbuzz_upto (i)))) (PreH18 : (0 <= count)) (PreH19 : (count <= (i * i ))) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 46340)) ,
  TT && emp
|--
  “ (((count_2 + 1 ) + (count_digit7 ((q ÷ 10 ))) ) <= (i_2 * (i_2 + 1 ) )) ”
.

Definition fizz_buzz_entail_wit_5_1_split_goal_2 :=
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (i_2 < n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (0 <= count_2)) (PreH7 : ((i_2 % ( 13 ) ) = 0)) (PreH8 : ((i_2 % ( 11 ) ) <> 0)) (PreH9 : (0 <= q)) (PreH10 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH11 : ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH12 : ((i % ( 13 ) ) = 0)) (PreH13 : ((i % ( 11 ) ) <> 0)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (count = (fizzbuzz_upto (i)))) (PreH18 : (0 <= count)) (PreH19 : (count <= (i * i ))) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 46340)) ,
  TT && emp
|--
  “ (((count_2 + 1 ) + (count_digit7 ((q ÷ 10 ))) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) ”
.

Definition fizz_buzz_entail_wit_5_1_split_goal_3 :=
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (i_2 < n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (0 <= count_2)) (PreH7 : ((i_2 % ( 13 ) ) = 0)) (PreH8 : ((i_2 % ( 11 ) ) <> 0)) (PreH9 : (0 <= q)) (PreH10 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH11 : ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH12 : ((i % ( 13 ) ) = 0)) (PreH13 : ((i % ( 11 ) ) <> 0)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (count = (fizzbuzz_upto (i)))) (PreH18 : (0 <= count)) (PreH19 : (count <= (i * i ))) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 46340)) ,
  TT && emp
|--
  “ (0 <= (q ÷ 10 )) ”
.

Definition fizz_buzz_entail_wit_5_2 :=
(
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) (PreH1 : ((q % ( 10 ) ) <> 7)) (PreH2 : (q > 0)) (PreH3 : (i_2 < n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (0 <= count_2)) (PreH7 : ((i_2 % ( 13 ) ) = 0)) (PreH8 : ((i_2 % ( 11 ) ) <> 0)) (PreH9 : (0 <= q)) (PreH10 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH11 : ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH12 : ((i % ( 13 ) ) = 0)) (PreH13 : ((i % ( 11 ) ) <> 0)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (count = (fizzbuzz_upto (i)))) (PreH18 : (0 <= count)) (PreH19 : (count <= (i * i ))) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 46340)) ,
  TT && emp
|--
  “ (i_2 < n_pre) ”
  &&  “ (0 <= i_2) ”
  &&  “ (i_2 <= n_pre) ”
  &&  “ (0 <= count_2) ”
  &&  “ ((i_2 % ( 13 ) ) = 0) ”
  &&  “ ((i_2 % ( 11 ) ) <> 0) ”
  &&  “ (0 <= (q ÷ 10 )) ”
  &&  “ ((count_2 + (count_digit7 ((q ÷ 10 ))) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) ”
  &&  “ ((count_2 + (count_digit7 ((q ÷ 10 ))) ) <= (i_2 * (i_2 + 1 ) )) ”
  &&  “ ((i % ( 13 ) ) = 0) ”
  &&  “ ((i % ( 11 ) ) <> 0) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (count = (fizzbuzz_upto (i))) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= (i * i )) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 46340) ”
  &&  emp
) \/
(
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) (PreH1 : ((q % ( 10 ) ) <> 7)) (PreH2 : (q > 0)) (PreH3 : (i_2 < n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (0 <= count_2)) (PreH7 : ((i_2 % ( 13 ) ) = 0)) (PreH8 : ((i_2 % ( 11 ) ) <> 0)) (PreH9 : (0 <= q)) (PreH10 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH11 : ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH12 : ((i % ( 13 ) ) = 0)) (PreH13 : ((i % ( 11 ) ) <> 0)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (count = (fizzbuzz_upto (i)))) (PreH18 : (0 <= count)) (PreH19 : (count <= (i * i ))) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 46340)) ,
  TT && emp
|--
  “ ((count_2 + (count_digit7 ((q ÷ 10 ))) ) <= (i_2 * (i_2 + 1 ) )) ”
  &&  “ ((count_2 + (count_digit7 ((q ÷ 10 ))) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) ”
  &&  “ (0 <= (q ÷ 10 )) ”
  &&  emp
).

Definition fizz_buzz_entail_wit_5_2_split_goal_1 :=
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) (PreH1 : ((q % ( 10 ) ) <> 7)) (PreH2 : (q > 0)) (PreH3 : (i_2 < n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (0 <= count_2)) (PreH7 : ((i_2 % ( 13 ) ) = 0)) (PreH8 : ((i_2 % ( 11 ) ) <> 0)) (PreH9 : (0 <= q)) (PreH10 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH11 : ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH12 : ((i % ( 13 ) ) = 0)) (PreH13 : ((i % ( 11 ) ) <> 0)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (count = (fizzbuzz_upto (i)))) (PreH18 : (0 <= count)) (PreH19 : (count <= (i * i ))) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 46340)) ,
  TT && emp
|--
  “ ((count_2 + (count_digit7 ((q ÷ 10 ))) ) <= (i_2 * (i_2 + 1 ) )) ”
.

Definition fizz_buzz_entail_wit_5_2_split_goal_2 :=
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) (PreH1 : ((q % ( 10 ) ) <> 7)) (PreH2 : (q > 0)) (PreH3 : (i_2 < n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (0 <= count_2)) (PreH7 : ((i_2 % ( 13 ) ) = 0)) (PreH8 : ((i_2 % ( 11 ) ) <> 0)) (PreH9 : (0 <= q)) (PreH10 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH11 : ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH12 : ((i % ( 13 ) ) = 0)) (PreH13 : ((i % ( 11 ) ) <> 0)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (count = (fizzbuzz_upto (i)))) (PreH18 : (0 <= count)) (PreH19 : (count <= (i * i ))) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 46340)) ,
  TT && emp
|--
  “ ((count_2 + (count_digit7 ((q ÷ 10 ))) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) ”
.

Definition fizz_buzz_entail_wit_5_2_split_goal_3 :=
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) (PreH1 : ((q % ( 10 ) ) <> 7)) (PreH2 : (q > 0)) (PreH3 : (i_2 < n_pre)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (0 <= count_2)) (PreH7 : ((i_2 % ( 13 ) ) = 0)) (PreH8 : ((i_2 % ( 11 ) ) <> 0)) (PreH9 : (0 <= q)) (PreH10 : ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) ))) (PreH11 : ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) ))) (PreH12 : ((i % ( 13 ) ) = 0)) (PreH13 : ((i % ( 11 ) ) <> 0)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (count = (fizzbuzz_upto (i)))) (PreH18 : (0 <= count)) (PreH19 : (count <= (i * i ))) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 46340)) ,
  TT && emp
|--
  “ (0 <= (q ÷ 10 )) ”
.

Definition fizz_buzz_entail_wit_6_1 :=
(
forall (n_pre: Z) (count_2: Z) (i_2: Z) (q: Z) (count: Z) (i: Z) (PreH1 : (q <= 0)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= count)) (PreH6 : ((i % ( 11 ) ) = 0)) (PreH7 : (0 <= q)) (PreH8 : ((count + (count_digit7 (q)) ) = ((fizzbuzz_upto (i)) + (count_digit7 (i)) ))) (PreH9 : ((count + (count_digit7 (q)) ) <= (i * (i + 1 ) ))) (PreH10 : ((i_2 % ( 11 ) ) = 0)) (PreH11 : (i_2 < n_pre)) (PreH12 : (0 <= i_2)) (PreH13 : (i_2 <= n_pre)) (PreH14 : (count_2 = (fizzbuzz_upto (i_2)))) (PreH15 : (0 <= count_2)) (PreH16 : (count_2 <= (i_2 * i_2 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 46340)) ,
  ((( &( "q" ) )) # Int  |-> q)
|--
  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (count = (fizzbuzz_upto ((i + 1 )))) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= ((i + 1 ) * (i + 1 ) )) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 46340) ”
  &&  ((( &( "q" ) )) # Int  |->_)
) \/
(
forall (n_pre: Z) (count_2: Z) (i_2: Z) (q: Z) (count: Z) (i: Z) (PreH1 : (q <= 0)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= count)) (PreH6 : ((i % ( 11 ) ) = 0)) (PreH7 : (0 <= q)) (PreH8 : ((count + (count_digit7 (q)) ) = ((fizzbuzz_upto (i)) + (count_digit7 (i)) ))) (PreH9 : ((count + (count_digit7 (q)) ) <= (i * (i + 1 ) ))) (PreH10 : ((i_2 % ( 11 ) ) = 0)) (PreH11 : (i_2 < n_pre)) (PreH12 : (0 <= i_2)) (PreH13 : (i_2 <= n_pre)) (PreH14 : (count_2 = (fizzbuzz_upto (i_2)))) (PreH15 : (0 <= count_2)) (PreH16 : (count_2 <= (i_2 * i_2 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 46340)) ,
  TT && emp
|--
  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (count = (fizzbuzz_upto ((i + 1 )))) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= ((i + 1 ) * (i + 1 ) )) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 46340) ”
  &&  emp
).

Definition fizz_buzz_entail_wit_6_2 :=
(
forall (n_pre: Z) (count_2: Z) (i_2: Z) (q: Z) (count: Z) (i: Z) (PreH1 : (q <= 0)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= count)) (PreH6 : ((i % ( 13 ) ) = 0)) (PreH7 : ((i % ( 11 ) ) <> 0)) (PreH8 : (0 <= q)) (PreH9 : ((count + (count_digit7 (q)) ) = ((fizzbuzz_upto (i)) + (count_digit7 (i)) ))) (PreH10 : ((count + (count_digit7 (q)) ) <= (i * (i + 1 ) ))) (PreH11 : ((i_2 % ( 13 ) ) = 0)) (PreH12 : ((i_2 % ( 11 ) ) <> 0)) (PreH13 : (i_2 < n_pre)) (PreH14 : (0 <= i_2)) (PreH15 : (i_2 <= n_pre)) (PreH16 : (count_2 = (fizzbuzz_upto (i_2)))) (PreH17 : (0 <= count_2)) (PreH18 : (count_2 <= (i_2 * i_2 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 46340)) ,
  ((( &( "q" ) )) # Int  |-> q)
|--
  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (count = (fizzbuzz_upto ((i + 1 )))) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= ((i + 1 ) * (i + 1 ) )) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 46340) ”
  &&  ((( &( "q" ) )) # Int  |->_)
) \/
(
forall (n_pre: Z) (count_2: Z) (i_2: Z) (q: Z) (count: Z) (i: Z) (PreH1 : (q <= 0)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= count)) (PreH6 : ((i % ( 13 ) ) = 0)) (PreH7 : ((i % ( 11 ) ) <> 0)) (PreH8 : (0 <= q)) (PreH9 : ((count + (count_digit7 (q)) ) = ((fizzbuzz_upto (i)) + (count_digit7 (i)) ))) (PreH10 : ((count + (count_digit7 (q)) ) <= (i * (i + 1 ) ))) (PreH11 : ((i_2 % ( 13 ) ) = 0)) (PreH12 : ((i_2 % ( 11 ) ) <> 0)) (PreH13 : (i_2 < n_pre)) (PreH14 : (0 <= i_2)) (PreH15 : (i_2 <= n_pre)) (PreH16 : (count_2 = (fizzbuzz_upto (i_2)))) (PreH17 : (0 <= count_2)) (PreH18 : (count_2 <= (i_2 * i_2 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 46340)) ,
  TT && emp
|--
  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (count = (fizzbuzz_upto ((i + 1 )))) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= ((i + 1 ) * (i + 1 ) )) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 46340) ”
  &&  emp
).

Definition fizz_buzz_entail_wit_6_3 :=
(
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : ((i % ( 13 ) ) <> 0)) (PreH2 : ((i % ( 11 ) ) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (count = (fizzbuzz_upto (i)))) (PreH7 : (0 <= count)) (PreH8 : (count <= (i * i ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 46340)) ,
  TT && emp
|--
  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (count = (fizzbuzz_upto ((i + 1 )))) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= ((i + 1 ) * (i + 1 ) )) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 46340) ”
  &&  emp
) \/
(
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : ((i % ( 13 ) ) <> 0)) (PreH2 : ((i % ( 11 ) ) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (count = (fizzbuzz_upto (i)))) (PreH7 : (0 <= count)) (PreH8 : (count <= (i * i ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 46340)) ,
  TT && emp
|--
  “ (count <= ((i + 1 ) * (i + 1 ) )) ”
  &&  “ (count = (fizzbuzz_upto ((i + 1 )))) ”
  &&  emp
).

Definition fizz_buzz_entail_wit_6_3_split_goal_1 :=
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : ((i % ( 13 ) ) <> 0)) (PreH2 : ((i % ( 11 ) ) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (count = (fizzbuzz_upto (i)))) (PreH7 : (0 <= count)) (PreH8 : (count <= (i * i ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 46340)) ,
  TT && emp
|--
  “ (count <= ((i + 1 ) * (i + 1 ) )) ”
.

Definition fizz_buzz_entail_wit_6_3_split_goal_2 :=
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : ((i % ( 13 ) ) <> 0)) (PreH2 : ((i % ( 11 ) ) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (count = (fizzbuzz_upto (i)))) (PreH7 : (0 <= count)) (PreH8 : (count <= (i * i ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 46340)) ,
  TT && emp
|--
  “ (count = (fizzbuzz_upto ((i + 1 )))) ”
.

Definition fizz_buzz_return_wit_1 :=
(
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (count = (fizzbuzz_upto (i)))) (PreH5 : (0 <= count)) (PreH6 : (count <= (i * i ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 46340)) ,
  TT && emp
|--
  “ (problem_36_spec_z n_pre count ) ”
  &&  emp
) \/
(
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (count = (fizzbuzz_upto (i)))) (PreH5 : (0 <= count)) (PreH6 : (count <= (i * i ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 46340)) ,
  TT && emp
|--
  “ (problem_36_spec_z n_pre count ) ”
  &&  emp
).

Definition fizz_buzz_return_wit_1_split_goal_1 :=
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (count = (fizzbuzz_upto (i)))) (PreH5 : (0 <= count)) (PreH6 : (count <= (i * i ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 46340)) ,
  TT && emp
|--
  “ (problem_36_spec_z n_pre count ) ”
.

Module Type VC_Correct.


Axiom proof_of_fizz_buzz_safety_wit_1 : fizz_buzz_safety_wit_1.
Axiom proof_of_fizz_buzz_safety_wit_2 : fizz_buzz_safety_wit_2.
Axiom proof_of_fizz_buzz_safety_wit_3 : fizz_buzz_safety_wit_3.
Axiom proof_of_fizz_buzz_safety_wit_4 : fizz_buzz_safety_wit_4.
Axiom proof_of_fizz_buzz_safety_wit_5 : fizz_buzz_safety_wit_5.
Axiom proof_of_fizz_buzz_safety_wit_6 : fizz_buzz_safety_wit_6.
Axiom proof_of_fizz_buzz_safety_wit_7 : fizz_buzz_safety_wit_7.
Axiom proof_of_fizz_buzz_safety_wit_8 : fizz_buzz_safety_wit_8.
Axiom proof_of_fizz_buzz_safety_wit_9 : fizz_buzz_safety_wit_9.
Axiom proof_of_fizz_buzz_safety_wit_10 : fizz_buzz_safety_wit_10.
Axiom proof_of_fizz_buzz_safety_wit_11 : fizz_buzz_safety_wit_11.
Axiom proof_of_fizz_buzz_safety_wit_12 : fizz_buzz_safety_wit_12.
Axiom proof_of_fizz_buzz_safety_wit_13 : fizz_buzz_safety_wit_13.
Axiom proof_of_fizz_buzz_safety_wit_14 : fizz_buzz_safety_wit_14.
Axiom proof_of_fizz_buzz_safety_wit_15 : fizz_buzz_safety_wit_15.
Axiom proof_of_fizz_buzz_safety_wit_16 : fizz_buzz_safety_wit_16.
Axiom proof_of_fizz_buzz_safety_wit_17 : fizz_buzz_safety_wit_17.
Axiom proof_of_fizz_buzz_safety_wit_18 : fizz_buzz_safety_wit_18.
Axiom proof_of_fizz_buzz_safety_wit_19 : fizz_buzz_safety_wit_19.
Axiom proof_of_fizz_buzz_safety_wit_20 : fizz_buzz_safety_wit_20.
Axiom proof_of_fizz_buzz_safety_wit_21 : fizz_buzz_safety_wit_21.
Axiom proof_of_fizz_buzz_safety_wit_22 : fizz_buzz_safety_wit_22.
Axiom proof_of_fizz_buzz_safety_wit_23 : fizz_buzz_safety_wit_23.
Axiom proof_of_fizz_buzz_safety_wit_24 : fizz_buzz_safety_wit_24.
Axiom proof_of_fizz_buzz_safety_wit_25 : fizz_buzz_safety_wit_25.
Axiom proof_of_fizz_buzz_safety_wit_26 : fizz_buzz_safety_wit_26.
Axiom proof_of_fizz_buzz_safety_wit_27 : fizz_buzz_safety_wit_27.
Axiom proof_of_fizz_buzz_safety_wit_28 : fizz_buzz_safety_wit_28.
Axiom proof_of_fizz_buzz_safety_wit_29 : fizz_buzz_safety_wit_29.
Axiom proof_of_fizz_buzz_safety_wit_30 : fizz_buzz_safety_wit_30.
Axiom proof_of_fizz_buzz_safety_wit_31 : fizz_buzz_safety_wit_31.
Axiom proof_of_fizz_buzz_entail_wit_1 : fizz_buzz_entail_wit_1.
Axiom proof_of_fizz_buzz_entail_wit_2 : fizz_buzz_entail_wit_2.
Axiom proof_of_fizz_buzz_entail_wit_3_1 : fizz_buzz_entail_wit_3_1.
Axiom proof_of_fizz_buzz_entail_wit_3_2 : fizz_buzz_entail_wit_3_2.
Axiom proof_of_fizz_buzz_entail_wit_4 : fizz_buzz_entail_wit_4.
Axiom proof_of_fizz_buzz_entail_wit_5_1 : fizz_buzz_entail_wit_5_1.
Axiom proof_of_fizz_buzz_entail_wit_5_2 : fizz_buzz_entail_wit_5_2.
Axiom proof_of_fizz_buzz_entail_wit_6_1 : fizz_buzz_entail_wit_6_1.
Axiom proof_of_fizz_buzz_entail_wit_6_2 : fizz_buzz_entail_wit_6_2.
Axiom proof_of_fizz_buzz_entail_wit_6_3 : fizz_buzz_entail_wit_6_3.
Axiom proof_of_fizz_buzz_return_wit_1 : fizz_buzz_return_wit_1.

End VC_Correct.
