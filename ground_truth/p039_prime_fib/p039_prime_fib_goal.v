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
Require Import p039_prime_fib.
Local Open Scope sac.

(*----- Function prime_fib -----*)

Definition prime_fib_safety_wit_1 :=
forall (n_pre: Z) (PreH1 : (problem_39_pre_z n_pre )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5)) ,
  ((( &( "m" ) )) # Int  |->_)
  **  ((( &( "f2" ) )) # Int  |->_)
  **  ((( &( "f1" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition prime_fib_safety_wit_2 :=
forall (n_pre: Z) (PreH1 : (problem_39_pre_z n_pre )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5)) ,
  ((( &( "m" ) )) # Int  |->_)
  **  ((( &( "f2" ) )) # Int  |->_)
  **  ((( &( "f1" ) )) # Int  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition prime_fib_safety_wit_3 :=
forall (n_pre: Z) (PreH1 : (problem_39_pre_z n_pre )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5)) ,
  ((( &( "count" ) )) # Int  |->_)
  **  ((( &( "m" ) )) # Int  |->_)
  **  ((( &( "f2" ) )) # Int  |-> 2)
  **  ((( &( "f1" ) )) # Int  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prime_fib_safety_wit_4 :=
forall (n_pre: Z) (f2: Z) (f1: Z) (count: Z) (PreH1 : (count >= n_pre)) (PreH2 : (0 <= count)) (PreH3 : (count < n_pre)) (PreH4 : (pf_state count f2 (f1 + f2 ) )) (PreH5 : (problem_39_pre_z n_pre )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 5)) ,
  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "f1" ) )) # Int  |-> f1)
  **  ((( &( "f2" ) )) # Int  |-> f2)
  **  ((( &( "m" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ False ”
.

Definition prime_fib_safety_wit_5 :=
(
forall (n_pre: Z) (f2: Z) (f1: Z) (count: Z) (PreH1 : (count < n_pre)) (PreH2 : (0 <= count)) (PreH3 : (count < n_pre)) (PreH4 : (pf_state count f2 (f1 + f2 ) )) (PreH5 : (problem_39_pre_z n_pre )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 5)) ,
  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "f1" ) )) # Int  |-> f1)
  **  ((( &( "f2" ) )) # Int  |-> f2)
  **  ((( &( "m" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((f1 + f2 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (f1 + f2 )) ”
) \/
(
forall (n_pre: Z) (f2: Z) (f1: Z) (count: Z) (PreH1 : (count < n_pre)) (PreH2 : (0 <= count)) (PreH3 : (count < n_pre)) (PreH4 : (pf_state count f2 (f1 + f2 ) )) (PreH5 : (problem_39_pre_z n_pre )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 5)) ,
  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "f1" ) )) # Int  |-> f1)
  **  ((( &( "f2" ) )) # Int  |-> f2)
  **  ((( &( "m" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((f1 + f2 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (f1 + f2 )) ”
).

Definition prime_fib_safety_wit_5_split_goal_1 :=
forall (n_pre: Z) (f2: Z) (f1: Z) (count: Z) (PreH1 : (count < n_pre)) (PreH2 : (0 <= count)) (PreH3 : (count < n_pre)) (PreH4 : (pf_state count f2 (f1 + f2 ) )) (PreH5 : (problem_39_pre_z n_pre )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 5)) ,
  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "f1" ) )) # Int  |-> f1)
  **  ((( &( "f2" ) )) # Int  |-> f2)
  **  ((( &( "m" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((f1 + f2 ) <= INT_MAX) ”
.

Definition prime_fib_safety_wit_5_split_goal_2 :=
forall (n_pre: Z) (f2: Z) (f1: Z) (count: Z) (PreH1 : (count < n_pre)) (PreH2 : (0 <= count)) (PreH3 : (count < n_pre)) (PreH4 : (pf_state count f2 (f1 + f2 ) )) (PreH5 : (problem_39_pre_z n_pre )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 5)) ,
  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "f1" ) )) # Int  |-> f1)
  **  ((( &( "f2" ) )) # Int  |-> f2)
  **  ((( &( "m" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((INT_MIN) <= (f1 + f2 )) ”
.

Definition prime_fib_safety_wit_6 :=
forall (n_pre: Z) (f2: Z) (f1: Z) (count: Z) (PreH1 : (count < n_pre)) (PreH2 : (0 <= count)) (PreH3 : (count < n_pre)) (PreH4 : (pf_state count f2 (f1 + f2 ) )) (PreH5 : (problem_39_pre_z n_pre )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 5)) ,
  ((( &( "isprime" ) )) # Int  |->_)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "f1" ) )) # Int  |-> f2)
  **  ((( &( "f2" ) )) # Int  |-> (f1 + f2 ))
  **  ((( &( "m" ) )) # Int  |-> (f1 + f2 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition prime_fib_safety_wit_7 :=
forall (n_pre: Z) (f2: Z) (f1: Z) (count: Z) (PreH1 : (count < n_pre)) (PreH2 : (0 <= count)) (PreH3 : (count < n_pre)) (PreH4 : (pf_state count f2 (f1 + f2 ) )) (PreH5 : (problem_39_pre_z n_pre )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 5)) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "isprime" ) )) # Int  |-> 1)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "f1" ) )) # Int  |-> f2)
  **  ((( &( "f2" ) )) # Int  |-> (f1 + f2 ))
  **  ((( &( "m" ) )) # Int  |-> (f1 + f2 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition prime_fib_safety_wit_8 :=
(
forall (n_pre: Z) (f2: Z) (f1: Z) (count: Z) (isprime: Z) (f2_2: Z) (f1_2: Z) (w: Z) (count_2: Z) (PreH1 : (0 <= count_2)) (PreH2 : (count_2 < n_pre)) (PreH3 : (2 <= w)) (PreH4 : (2 <= f1_2)) (PreH5 : (f1_2 <= 144)) (PreH6 : (pf_state count_2 f1_2 f2_2 )) (PreH7 : (w <= (f1_2 + 1 ))) (PreH8 : ((isprime = 0) -> (((((f1_2 <> 2) /\ (f1_2 <> 3)) /\ (f1_2 <> 5)) /\ (f1_2 <> 13)) /\ (f1_2 <> 89)))) (PreH9 : ((isprime <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < w)) -> ((f1_2 % ( k ) ) <> 0)))) (PreH10 : (count < n_pre)) (PreH11 : (0 <= count)) (PreH12 : (count < n_pre)) (PreH13 : (pf_state count f2 (f1 + f2 ) )) (PreH14 : (problem_39_pre_z n_pre )) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 5)) ,
  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "f1" ) )) # Int  |-> f1_2)
  **  ((( &( "f2" ) )) # Int  |-> f2_2)
  **  ((( &( "isprime" ) )) # Int  |-> isprime)
  **  ((( &( "m" ) )) # Int  |-> (f1 + f2 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((w * w ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (w * w )) ”
) \/
(
forall (n_pre: Z) (f2: Z) (f1: Z) (count: Z) (isprime: Z) (f2_2: Z) (f1_2: Z) (w: Z) (count_2: Z) (PreH1 : (0 <= count_2)) (PreH2 : (count_2 < n_pre)) (PreH3 : (2 <= w)) (PreH4 : (2 <= f1_2)) (PreH5 : (f1_2 <= 144)) (PreH6 : (pf_state count_2 f1_2 f2_2 )) (PreH7 : (w <= (f1_2 + 1 ))) (PreH8 : ((isprime = 0) -> (((((f1_2 <> 2) /\ (f1_2 <> 3)) /\ (f1_2 <> 5)) /\ (f1_2 <> 13)) /\ (f1_2 <> 89)))) (PreH9 : ((isprime <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < w)) -> ((f1_2 % ( k ) ) <> 0)))) (PreH10 : (count < n_pre)) (PreH11 : (0 <= count)) (PreH12 : (count < n_pre)) (PreH13 : (pf_state count f2 (f1 + f2 ) )) (PreH14 : (problem_39_pre_z n_pre )) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 5)) ,
  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "f1" ) )) # Int  |-> f1_2)
  **  ((( &( "f2" ) )) # Int  |-> f2_2)
  **  ((( &( "isprime" ) )) # Int  |-> isprime)
  **  ((( &( "m" ) )) # Int  |-> (f1 + f2 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((w * w ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (w * w )) ”
).

Definition prime_fib_safety_wit_8_split_goal_1 :=
forall (n_pre: Z) (f2: Z) (f1: Z) (count: Z) (isprime: Z) (f2_2: Z) (f1_2: Z) (w: Z) (count_2: Z) (PreH1 : (0 <= count_2)) (PreH2 : (count_2 < n_pre)) (PreH3 : (2 <= w)) (PreH4 : (2 <= f1_2)) (PreH5 : (f1_2 <= 144)) (PreH6 : (pf_state count_2 f1_2 f2_2 )) (PreH7 : (w <= (f1_2 + 1 ))) (PreH8 : ((isprime = 0) -> (((((f1_2 <> 2) /\ (f1_2 <> 3)) /\ (f1_2 <> 5)) /\ (f1_2 <> 13)) /\ (f1_2 <> 89)))) (PreH9 : ((isprime <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < w)) -> ((f1_2 % ( k ) ) <> 0)))) (PreH10 : (count < n_pre)) (PreH11 : (0 <= count)) (PreH12 : (count < n_pre)) (PreH13 : (pf_state count f2 (f1 + f2 ) )) (PreH14 : (problem_39_pre_z n_pre )) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 5)) ,
  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "f1" ) )) # Int  |-> f1_2)
  **  ((( &( "f2" ) )) # Int  |-> f2_2)
  **  ((( &( "isprime" ) )) # Int  |-> isprime)
  **  ((( &( "m" ) )) # Int  |-> (f1 + f2 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((w * w ) <= INT_MAX) ”
.

Definition prime_fib_safety_wit_8_split_goal_2 :=
forall (n_pre: Z) (f2: Z) (f1: Z) (count: Z) (isprime: Z) (f2_2: Z) (f1_2: Z) (w: Z) (count_2: Z) (PreH1 : (0 <= count_2)) (PreH2 : (count_2 < n_pre)) (PreH3 : (2 <= w)) (PreH4 : (2 <= f1_2)) (PreH5 : (f1_2 <= 144)) (PreH6 : (pf_state count_2 f1_2 f2_2 )) (PreH7 : (w <= (f1_2 + 1 ))) (PreH8 : ((isprime = 0) -> (((((f1_2 <> 2) /\ (f1_2 <> 3)) /\ (f1_2 <> 5)) /\ (f1_2 <> 13)) /\ (f1_2 <> 89)))) (PreH9 : ((isprime <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < w)) -> ((f1_2 % ( k ) ) <> 0)))) (PreH10 : (count < n_pre)) (PreH11 : (0 <= count)) (PreH12 : (count < n_pre)) (PreH13 : (pf_state count f2 (f1 + f2 ) )) (PreH14 : (problem_39_pre_z n_pre )) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 5)) ,
  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "f1" ) )) # Int  |-> f1_2)
  **  ((( &( "f2" ) )) # Int  |-> f2_2)
  **  ((( &( "isprime" ) )) # Int  |-> isprime)
  **  ((( &( "m" ) )) # Int  |-> (f1 + f2 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((INT_MIN) <= (w * w )) ”
.

Definition prime_fib_safety_wit_9 :=
forall (n_pre: Z) (f2: Z) (f1_2: Z) (count: Z) (isprime: Z) (f2_2: Z) (f1: Z) (w: Z) (count_2: Z) (PreH1 : ((w * w ) <= f1)) (PreH2 : (0 <= count_2)) (PreH3 : (count_2 < n_pre)) (PreH4 : (2 <= w)) (PreH5 : (2 <= f1)) (PreH6 : (f1 <= 144)) (PreH7 : (pf_state count_2 f1 f2_2 )) (PreH8 : (w <= (f1 + 1 ))) (PreH9 : ((isprime = 0) -> (((((f1 <> 2) /\ (f1 <> 3)) /\ (f1 <> 5)) /\ (f1 <> 13)) /\ (f1 <> 89)))) (PreH10 : ((isprime <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < w)) -> ((f1 % ( k ) ) <> 0)))) (PreH11 : (count < n_pre)) (PreH12 : (0 <= count)) (PreH13 : (count < n_pre)) (PreH14 : (pf_state count f2 (f1_2 + f2 ) )) (PreH15 : (problem_39_pre_z n_pre )) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 5)) ,
  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "f1" ) )) # Int  |-> f1)
  **  ((( &( "f2" ) )) # Int  |-> f2_2)
  **  ((( &( "isprime" ) )) # Int  |-> isprime)
  **  ((( &( "m" ) )) # Int  |-> (f1_2 + f2 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((f1 <> (INT_MIN)) \/ (w <> (-1))) ”
  &&  “ (w <> 0) ”
.

Definition prime_fib_safety_wit_10 :=
forall (n_pre: Z) (f2: Z) (f1: Z) (count: Z) (isprime: Z) (f2_2: Z) (f1_2: Z) (w: Z) (count_2: Z) (PreH1 : ((w * w ) <= f1_2)) (PreH2 : (0 <= count_2)) (PreH3 : (count_2 < n_pre)) (PreH4 : (2 <= w)) (PreH5 : (2 <= f1_2)) (PreH6 : (f1_2 <= 144)) (PreH7 : (pf_state count_2 f1_2 f2_2 )) (PreH8 : (w <= (f1_2 + 1 ))) (PreH9 : ((isprime = 0) -> (((((f1_2 <> 2) /\ (f1_2 <> 3)) /\ (f1_2 <> 5)) /\ (f1_2 <> 13)) /\ (f1_2 <> 89)))) (PreH10 : ((isprime <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < w)) -> ((f1_2 % ( k ) ) <> 0)))) (PreH11 : (count < n_pre)) (PreH12 : (0 <= count)) (PreH13 : (count < n_pre)) (PreH14 : (pf_state count f2 (f1 + f2 ) )) (PreH15 : (problem_39_pre_z n_pre )) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 5)) ,
  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "f1" ) )) # Int  |-> f1_2)
  **  ((( &( "f2" ) )) # Int  |-> f2_2)
  **  ((( &( "isprime" ) )) # Int  |-> isprime)
  **  ((( &( "m" ) )) # Int  |-> (f1 + f2 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prime_fib_safety_wit_11 :=
forall (n_pre: Z) (f2: Z) (f1: Z) (count: Z) (isprime: Z) (f2_2: Z) (f1_2: Z) (w: Z) (count_2: Z) (PreH1 : ((f1_2 % ( w ) ) = 0)) (PreH2 : ((w * w ) <= f1_2)) (PreH3 : (0 <= count_2)) (PreH4 : (count_2 < n_pre)) (PreH5 : (2 <= w)) (PreH6 : (2 <= f1_2)) (PreH7 : (f1_2 <= 144)) (PreH8 : (pf_state count_2 f1_2 f2_2 )) (PreH9 : (w <= (f1_2 + 1 ))) (PreH10 : ((isprime = 0) -> (((((f1_2 <> 2) /\ (f1_2 <> 3)) /\ (f1_2 <> 5)) /\ (f1_2 <> 13)) /\ (f1_2 <> 89)))) (PreH11 : ((isprime <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < w)) -> ((f1_2 % ( k ) ) <> 0)))) (PreH12 : (count < n_pre)) (PreH13 : (0 <= count)) (PreH14 : (count < n_pre)) (PreH15 : (pf_state count f2 (f1 + f2 ) )) (PreH16 : (problem_39_pre_z n_pre )) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 5)) ,
  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "f1" ) )) # Int  |-> f1_2)
  **  ((( &( "f2" ) )) # Int  |-> f2_2)
  **  ((( &( "isprime" ) )) # Int  |-> isprime)
  **  ((( &( "m" ) )) # Int  |-> (f1 + f2 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prime_fib_safety_wit_12 :=
forall (n_pre: Z) (f2: Z) (f1: Z) (count: Z) (isprime: Z) (f2_2: Z) (f1_2: Z) (w: Z) (count_2: Z) (PreH1 : ((f1_2 % ( w ) ) <> 0)) (PreH2 : ((w * w ) <= f1_2)) (PreH3 : (0 <= count_2)) (PreH4 : (count_2 < n_pre)) (PreH5 : (2 <= w)) (PreH6 : (2 <= f1_2)) (PreH7 : (f1_2 <= 144)) (PreH8 : (pf_state count_2 f1_2 f2_2 )) (PreH9 : (w <= (f1_2 + 1 ))) (PreH10 : ((isprime = 0) -> (((((f1_2 <> 2) /\ (f1_2 <> 3)) /\ (f1_2 <> 5)) /\ (f1_2 <> 13)) /\ (f1_2 <> 89)))) (PreH11 : ((isprime <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < w)) -> ((f1_2 % ( k ) ) <> 0)))) (PreH12 : (count < n_pre)) (PreH13 : (0 <= count)) (PreH14 : (count < n_pre)) (PreH15 : (pf_state count f2 (f1 + f2 ) )) (PreH16 : (problem_39_pre_z n_pre )) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 5)) ,
  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "f1" ) )) # Int  |-> f1_2)
  **  ((( &( "f2" ) )) # Int  |-> f2_2)
  **  ((( &( "isprime" ) )) # Int  |-> isprime)
  **  ((( &( "m" ) )) # Int  |-> (f1 + f2 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((w + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (w + 1 )) ”
.

Definition prime_fib_safety_wit_13 :=
forall (n_pre: Z) (f2: Z) (f1: Z) (count_2: Z) (isprime: Z) (f2_2: Z) (f1_2: Z) (w: Z) (count: Z) (PreH1 : ((w * w ) > f1_2)) (PreH2 : (0 <= count)) (PreH3 : (count < n_pre)) (PreH4 : (2 <= w)) (PreH5 : (2 <= f1_2)) (PreH6 : (f1_2 <= 144)) (PreH7 : (pf_state count f1_2 f2_2 )) (PreH8 : (w <= (f1_2 + 1 ))) (PreH9 : ((isprime = 0) -> (((((f1_2 <> 2) /\ (f1_2 <> 3)) /\ (f1_2 <> 5)) /\ (f1_2 <> 13)) /\ (f1_2 <> 89)))) (PreH10 : ((isprime <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < w)) -> ((f1_2 % ( k ) ) <> 0)))) (PreH11 : (count_2 < n_pre)) (PreH12 : (0 <= count_2)) (PreH13 : (count_2 < n_pre)) (PreH14 : (pf_state count_2 f2 (f1 + f2 ) )) (PreH15 : (problem_39_pre_z n_pre )) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 5)) (PreH18 : (isprime <> 0)) ,
  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "f1" ) )) # Int  |-> f1_2)
  **  ((( &( "f2" ) )) # Int  |-> f2_2)
  **  ((( &( "isprime" ) )) # Int  |-> isprime)
  **  ((( &( "m" ) )) # Int  |-> (f1 + f2 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((count + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition prime_fib_safety_wit_14 :=
forall (n_pre: Z) (f2: Z) (f1: Z) (count: Z) (isprime: Z) (f2_2: Z) (f1_2: Z) (w: Z) (count_2: Z) (PreH1 : ((w * w ) > f1_2)) (PreH2 : (0 <= count_2)) (PreH3 : (count_2 < n_pre)) (PreH4 : (2 <= w)) (PreH5 : (2 <= f1_2)) (PreH6 : (f1_2 <= 144)) (PreH7 : (pf_state count_2 f1_2 f2_2 )) (PreH8 : (w <= (f1_2 + 1 ))) (PreH9 : ((isprime = 0) -> (((((f1_2 <> 2) /\ (f1_2 <> 3)) /\ (f1_2 <> 5)) /\ (f1_2 <> 13)) /\ (f1_2 <> 89)))) (PreH10 : ((isprime <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < w)) -> ((f1_2 % ( k ) ) <> 0)))) (PreH11 : (count < n_pre)) (PreH12 : (0 <= count)) (PreH13 : (count < n_pre)) (PreH14 : (pf_state count f2 (f1 + f2 ) )) (PreH15 : (problem_39_pre_z n_pre )) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 5)) (PreH18 : (isprime <> 0)) ,
  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "f1" ) )) # Int  |-> f1_2)
  **  ((( &( "f2" ) )) # Int  |-> f2_2)
  **  ((( &( "isprime" ) )) # Int  |-> isprime)
  **  ((( &( "m" ) )) # Int  |-> (f1 + f2 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition prime_fib_safety_wit_15 :=
forall (n_pre: Z) (f2: Z) (f1: Z) (count: Z) (isprime: Z) (f2_2: Z) (f1_2: Z) (w: Z) (count_2: Z) (PreH1 : (count_2 = n_pre)) (PreH2 : ((w * w ) > f1_2)) (PreH3 : (0 <= count_2)) (PreH4 : (count_2 < n_pre)) (PreH5 : (2 <= w)) (PreH6 : (2 <= f1_2)) (PreH7 : (f1_2 <= 144)) (PreH8 : (pf_state count_2 f1_2 f2_2 )) (PreH9 : (w <= (f1_2 + 1 ))) (PreH10 : ((isprime = 0) -> (((((f1_2 <> 2) /\ (f1_2 <> 3)) /\ (f1_2 <> 5)) /\ (f1_2 <> 13)) /\ (f1_2 <> 89)))) (PreH11 : ((isprime <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < w)) -> ((f1_2 % ( k ) ) <> 0)))) (PreH12 : (count < n_pre)) (PreH13 : (0 <= count)) (PreH14 : (count < n_pre)) (PreH15 : (pf_state count f2 (f1 + f2 ) )) (PreH16 : (problem_39_pre_z n_pre )) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 5)) (PreH19 : (isprime = 0)) ,
  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "f1" ) )) # Int  |-> f1_2)
  **  ((( &( "f2" ) )) # Int  |-> f2_2)
  **  ((( &( "isprime" ) )) # Int  |-> isprime)
  **  ((( &( "m" ) )) # Int  |-> (f1 + f2 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ False ”
.

Definition prime_fib_safety_wit_16 :=
forall (n_pre: Z) (f2: Z) (f1: Z) (count: Z) (isprime: Z) (f2_2: Z) (f1_2: Z) (w: Z) (count_2: Z) (PreH1 : (count_2 = n_pre)) (PreH2 : ((f1_2 % ( w ) ) = 0)) (PreH3 : ((w * w ) <= f1_2)) (PreH4 : (0 <= count_2)) (PreH5 : (count_2 < n_pre)) (PreH6 : (2 <= w)) (PreH7 : (2 <= f1_2)) (PreH8 : (f1_2 <= 144)) (PreH9 : (pf_state count_2 f1_2 f2_2 )) (PreH10 : (w <= (f1_2 + 1 ))) (PreH11 : ((isprime = 0) -> (((((f1_2 <> 2) /\ (f1_2 <> 3)) /\ (f1_2 <> 5)) /\ (f1_2 <> 13)) /\ (f1_2 <> 89)))) (PreH12 : ((isprime <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < w)) -> ((f1_2 % ( k ) ) <> 0)))) (PreH13 : (count < n_pre)) (PreH14 : (0 <= count)) (PreH15 : (count < n_pre)) (PreH16 : (pf_state count f2 (f1 + f2 ) )) (PreH17 : (problem_39_pre_z n_pre )) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 5)) ,
  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "f1" ) )) # Int  |-> f1_2)
  **  ((( &( "f2" ) )) # Int  |-> f2_2)
  **  ((( &( "isprime" ) )) # Int  |-> 0)
  **  ((( &( "m" ) )) # Int  |-> (f1 + f2 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ False ”
.

Definition prime_fib_entail_wit_1 :=
(
forall (n_pre: Z) (PreH1 : (problem_39_pre_z n_pre )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5)) ,
  TT && emp
|--
  “ (0 <= 0) ”
  &&  “ (0 < n_pre) ”
  &&  “ (pf_state 0 2 (1 + 2 ) ) ”
  &&  “ (problem_39_pre_z n_pre ) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 5) ”
  &&  emp
) \/
(
forall (n_pre: Z) (PreH1 : (problem_39_pre_z n_pre )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5)) ,
  TT && emp
|--
  “ (pf_state 0 2 (1 + 2 ) ) ”
  &&  emp
).

Definition prime_fib_entail_wit_1_split_goal_1 :=
forall (n_pre: Z) (PreH1 : (problem_39_pre_z n_pre )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5)) ,
  TT && emp
|--
  “ (pf_state 0 2 (1 + 2 ) ) ”
.

Definition prime_fib_entail_wit_2 :=
(
forall (n_pre: Z) (f2: Z) (f1: Z) (count: Z) (PreH1 : (count < n_pre)) (PreH2 : (0 <= count)) (PreH3 : (count < n_pre)) (PreH4 : (pf_state count f2 (f1 + f2 ) )) (PreH5 : (problem_39_pre_z n_pre )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 5)) ,
  TT && emp
|--
  “ (0 <= count) ”
  &&  “ (count < n_pre) ”
  &&  “ (2 <= 2) ”
  &&  “ (2 <= f2) ”
  &&  “ (f2 <= 144) ”
  &&  “ (pf_state count f2 (f1 + f2 ) ) ”
  &&  “ (2 <= (f2 + 1 )) ”
  &&  “ ((1 = 0) -> (((((f2 <> 2) /\ (f2 <> 3)) /\ (f2 <> 5)) /\ (f2 <> 13)) /\ (f2 <> 89))) ”
  &&  “ ((1 <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < 2)) -> ((f2 % ( k ) ) <> 0))) ”
  &&  “ (count < n_pre) ”
  &&  “ (0 <= count) ”
  &&  “ (count < n_pre) ”
  &&  “ (pf_state count f2 (f1 + f2 ) ) ”
  &&  “ (problem_39_pre_z n_pre ) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 5) ”
  &&  emp
) \/
(
forall (n_pre: Z) (f2: Z) (f1: Z) (count: Z) (PreH1 : (count < n_pre)) (PreH2 : (0 <= count)) (PreH3 : (count < n_pre)) (PreH4 : (pf_state count f2 (f1 + f2 ) )) (PreH5 : (problem_39_pre_z n_pre )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 5)) ,
  TT && emp
|--
  “ ((1 <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < 2)) -> ((f2 % ( k ) ) <> 0))) ”
  &&  “ (2 <= (f2 + 1 )) ”
  &&  “ (f2 <= 144) ”
  &&  “ (2 <= f2) ”
  &&  emp
).

Definition prime_fib_entail_wit_2_split_goal_1 :=
forall (n_pre: Z) (f2: Z) (f1: Z) (count: Z) (PreH1 : (count < n_pre)) (PreH2 : (0 <= count)) (PreH3 : (count < n_pre)) (PreH4 : (pf_state count f2 (f1 + f2 ) )) (PreH5 : (problem_39_pre_z n_pre )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 5)) ,
  TT && emp
|--
  “ ((1 <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < 2)) -> ((f2 % ( k ) ) <> 0))) ”
.

Definition prime_fib_entail_wit_2_split_goal_2 :=
forall (n_pre: Z) (f2: Z) (f1: Z) (count: Z) (PreH1 : (count < n_pre)) (PreH2 : (0 <= count)) (PreH3 : (count < n_pre)) (PreH4 : (pf_state count f2 (f1 + f2 ) )) (PreH5 : (problem_39_pre_z n_pre )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 5)) ,
  TT && emp
|--
  “ (2 <= (f2 + 1 )) ”
.

Definition prime_fib_entail_wit_2_split_goal_3 :=
forall (n_pre: Z) (f2: Z) (f1: Z) (count: Z) (PreH1 : (count < n_pre)) (PreH2 : (0 <= count)) (PreH3 : (count < n_pre)) (PreH4 : (pf_state count f2 (f1 + f2 ) )) (PreH5 : (problem_39_pre_z n_pre )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 5)) ,
  TT && emp
|--
  “ (f2 <= 144) ”
.

Definition prime_fib_entail_wit_2_split_goal_4 :=
forall (n_pre: Z) (f2: Z) (f1: Z) (count: Z) (PreH1 : (count < n_pre)) (PreH2 : (0 <= count)) (PreH3 : (count < n_pre)) (PreH4 : (pf_state count f2 (f1 + f2 ) )) (PreH5 : (problem_39_pre_z n_pre )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 5)) ,
  TT && emp
|--
  “ (2 <= f2) ”
.

Definition prime_fib_entail_wit_3 :=
(
forall (n_pre: Z) (f2: Z) (f1: Z) (count: Z) (isprime: Z) (f2_2: Z) (f1_2: Z) (w: Z) (count_2: Z) (PreH1 : ((f1_2 % ( w ) ) <> 0)) (PreH2 : ((w * w ) <= f1_2)) (PreH3 : (0 <= count_2)) (PreH4 : (count_2 < n_pre)) (PreH5 : (2 <= w)) (PreH6 : (2 <= f1_2)) (PreH7 : (f1_2 <= 144)) (PreH8 : (pf_state count_2 f1_2 f2_2 )) (PreH9 : (w <= (f1_2 + 1 ))) (PreH10 : ((isprime = 0) -> (((((f1_2 <> 2) /\ (f1_2 <> 3)) /\ (f1_2 <> 5)) /\ (f1_2 <> 13)) /\ (f1_2 <> 89)))) (PreH11 : ((isprime <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < w)) -> ((f1_2 % ( k ) ) <> 0)))) (PreH12 : (count < n_pre)) (PreH13 : (0 <= count)) (PreH14 : (count < n_pre)) (PreH15 : (pf_state count f2 (f1 + f2 ) )) (PreH16 : (problem_39_pre_z n_pre )) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 5)) ,
  TT && emp
|--
  “ (0 <= count_2) ”
  &&  “ (count_2 < n_pre) ”
  &&  “ (2 <= (w + 1 )) ”
  &&  “ (2 <= f1_2) ”
  &&  “ (f1_2 <= 144) ”
  &&  “ (pf_state count_2 f1_2 f2_2 ) ”
  &&  “ ((w + 1 ) <= (f1_2 + 1 )) ”
  &&  “ ((isprime = 0) -> (((((f1_2 <> 2) /\ (f1_2 <> 3)) /\ (f1_2 <> 5)) /\ (f1_2 <> 13)) /\ (f1_2 <> 89))) ”
  &&  “ ((isprime <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < (w + 1 ))) -> ((f1_2 % ( k ) ) <> 0))) ”
  &&  “ (count < n_pre) ”
  &&  “ (0 <= count) ”
  &&  “ (count < n_pre) ”
  &&  “ (pf_state count f2 (f1 + f2 ) ) ”
  &&  “ (problem_39_pre_z n_pre ) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 5) ”
  &&  emp
) \/
(
forall (n_pre: Z) (f2: Z) (f1: Z) (count: Z) (isprime: Z) (f2_2: Z) (f1_2: Z) (w: Z) (count_2: Z) (PreH1 : ((f1_2 % ( w ) ) <> 0)) (PreH2 : ((w * w ) <= f1_2)) (PreH3 : (0 <= count_2)) (PreH4 : (count_2 < n_pre)) (PreH5 : (2 <= w)) (PreH6 : (2 <= f1_2)) (PreH7 : (f1_2 <= 144)) (PreH8 : (pf_state count_2 f1_2 f2_2 )) (PreH9 : (w <= (f1_2 + 1 ))) (PreH10 : ((isprime = 0) -> (((((f1_2 <> 2) /\ (f1_2 <> 3)) /\ (f1_2 <> 5)) /\ (f1_2 <> 13)) /\ (f1_2 <> 89)))) (PreH11 : ((isprime <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < w)) -> ((f1_2 % ( k ) ) <> 0)))) (PreH12 : (count < n_pre)) (PreH13 : (0 <= count)) (PreH14 : (count < n_pre)) (PreH15 : (pf_state count f2 (f1 + f2 ) )) (PreH16 : (problem_39_pre_z n_pre )) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 5)) ,
  TT && emp
|--
  “ ((w + 1 ) <= (f1_2 + 1 )) ”
  &&  emp
).

Definition prime_fib_entail_wit_3_split_goal_1 :=
forall (n_pre: Z) (f2: Z) (f1: Z) (count: Z) (isprime: Z) (f2_2: Z) (f1_2: Z) (w: Z) (count_2: Z) (PreH1 : ((f1_2 % ( w ) ) <> 0)) (PreH2 : ((w * w ) <= f1_2)) (PreH3 : (0 <= count_2)) (PreH4 : (count_2 < n_pre)) (PreH5 : (2 <= w)) (PreH6 : (2 <= f1_2)) (PreH7 : (f1_2 <= 144)) (PreH8 : (pf_state count_2 f1_2 f2_2 )) (PreH9 : (w <= (f1_2 + 1 ))) (PreH10 : ((isprime = 0) -> (((((f1_2 <> 2) /\ (f1_2 <> 3)) /\ (f1_2 <> 5)) /\ (f1_2 <> 13)) /\ (f1_2 <> 89)))) (PreH11 : ((isprime <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < w)) -> ((f1_2 % ( k ) ) <> 0)))) (PreH12 : (count < n_pre)) (PreH13 : (0 <= count)) (PreH14 : (count < n_pre)) (PreH15 : (pf_state count f2 (f1 + f2 ) )) (PreH16 : (problem_39_pre_z n_pre )) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 5)) ,
  TT && emp
|--
  “ ((w + 1 ) <= (f1_2 + 1 )) ”
.

Definition prime_fib_entail_wit_4_1 :=
(
forall (n_pre: Z) (f2_2: Z) (f1_2: Z) (count_2: Z) (isprime: Z) (f2: Z) (f1: Z) (w: Z) (count: Z) (PreH1 : ((count + 1 ) <> n_pre)) (PreH2 : ((w * w ) > f1)) (PreH3 : (0 <= count)) (PreH4 : (count < n_pre)) (PreH5 : (2 <= w)) (PreH6 : (2 <= f1)) (PreH7 : (f1 <= 144)) (PreH8 : (pf_state count f1 f2 )) (PreH9 : (w <= (f1 + 1 ))) (PreH10 : ((isprime = 0) -> (((((f1 <> 2) /\ (f1 <> 3)) /\ (f1 <> 5)) /\ (f1 <> 13)) /\ (f1 <> 89)))) (PreH11 : ((isprime <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < w)) -> ((f1 % ( k ) ) <> 0)))) (PreH12 : (count_2 < n_pre)) (PreH13 : (0 <= count_2)) (PreH14 : (count_2 < n_pre)) (PreH15 : (pf_state count_2 f2_2 (f1_2 + f2_2 ) )) (PreH16 : (problem_39_pre_z n_pre )) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 5)) (PreH19 : (isprime <> 0)) ,
  ((( &( "m" ) )) # Int  |-> (f1_2 + f2_2 ))
|--
  “ (0 <= (count + 1 )) ”
  &&  “ ((count + 1 ) < n_pre) ”
  &&  “ (pf_state (count + 1 ) f2 (f1 + f2 ) ) ”
  &&  “ (problem_39_pre_z n_pre ) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 5) ”
  &&  ((( &( "m" ) )) # Int  |->_)
) \/
(
forall (n_pre: Z) (f2_2: Z) (f1_2: Z) (count_2: Z) (isprime: Z) (f2: Z) (f1: Z) (w: Z) (count: Z) (PreH1 : ((count + 1 ) <> n_pre)) (PreH2 : ((w * w ) > f1)) (PreH3 : (0 <= count)) (PreH4 : (count < n_pre)) (PreH5 : (2 <= w)) (PreH6 : (2 <= f1)) (PreH7 : (f1 <= 144)) (PreH8 : (pf_state count f1 f2 )) (PreH9 : (w <= (f1 + 1 ))) (PreH10 : ((isprime = 0) -> (((((f1 <> 2) /\ (f1 <> 3)) /\ (f1 <> 5)) /\ (f1 <> 13)) /\ (f1 <> 89)))) (PreH11 : ((isprime <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < w)) -> ((f1 % ( k ) ) <> 0)))) (PreH12 : (count_2 < n_pre)) (PreH13 : (0 <= count_2)) (PreH14 : (count_2 < n_pre)) (PreH15 : (pf_state count_2 f2_2 (f1_2 + f2_2 ) )) (PreH16 : (problem_39_pre_z n_pre )) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 5)) (PreH19 : (isprime <> 0)) ,
  TT && emp
|--
  “ (pf_state (count + 1 ) f2 (f1 + f2 ) ) ”
  &&  emp
).

Definition prime_fib_entail_wit_4_1_split_goal_1 :=
forall (n_pre: Z) (f2_2: Z) (f1_2: Z) (count_2: Z) (isprime: Z) (f2: Z) (f1: Z) (w: Z) (count: Z) (PreH1 : ((count + 1 ) <> n_pre)) (PreH2 : ((w * w ) > f1)) (PreH3 : (0 <= count)) (PreH4 : (count < n_pre)) (PreH5 : (2 <= w)) (PreH6 : (2 <= f1)) (PreH7 : (f1 <= 144)) (PreH8 : (pf_state count f1 f2 )) (PreH9 : (w <= (f1 + 1 ))) (PreH10 : ((isprime = 0) -> (((((f1 <> 2) /\ (f1 <> 3)) /\ (f1 <> 5)) /\ (f1 <> 13)) /\ (f1 <> 89)))) (PreH11 : ((isprime <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < w)) -> ((f1 % ( k ) ) <> 0)))) (PreH12 : (count_2 < n_pre)) (PreH13 : (0 <= count_2)) (PreH14 : (count_2 < n_pre)) (PreH15 : (pf_state count_2 f2_2 (f1_2 + f2_2 ) )) (PreH16 : (problem_39_pre_z n_pre )) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 5)) (PreH19 : (isprime <> 0)) ,
  TT && emp
|--
  “ (pf_state (count + 1 ) f2 (f1 + f2 ) ) ”
.

Definition prime_fib_entail_wit_4_2 :=
(
forall (n_pre: Z) (f2_2: Z) (f1_2: Z) (count_2: Z) (isprime: Z) (f2: Z) (f1: Z) (w: Z) (count: Z) (PreH1 : (count <> n_pre)) (PreH2 : ((w * w ) > f1)) (PreH3 : (0 <= count)) (PreH4 : (count < n_pre)) (PreH5 : (2 <= w)) (PreH6 : (2 <= f1)) (PreH7 : (f1 <= 144)) (PreH8 : (pf_state count f1 f2 )) (PreH9 : (w <= (f1 + 1 ))) (PreH10 : ((isprime = 0) -> (((((f1 <> 2) /\ (f1 <> 3)) /\ (f1 <> 5)) /\ (f1 <> 13)) /\ (f1 <> 89)))) (PreH11 : ((isprime <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < w)) -> ((f1 % ( k ) ) <> 0)))) (PreH12 : (count_2 < n_pre)) (PreH13 : (0 <= count_2)) (PreH14 : (count_2 < n_pre)) (PreH15 : (pf_state count_2 f2_2 (f1_2 + f2_2 ) )) (PreH16 : (problem_39_pre_z n_pre )) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 5)) (PreH19 : (isprime = 0)) ,
  ((( &( "m" ) )) # Int  |-> (f1_2 + f2_2 ))
|--
  “ (0 <= count) ”
  &&  “ (count < n_pre) ”
  &&  “ (pf_state count f2 (f1 + f2 ) ) ”
  &&  “ (problem_39_pre_z n_pre ) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 5) ”
  &&  ((( &( "m" ) )) # Int  |->_)
) \/
(
forall (n_pre: Z) (f2_2: Z) (f1_2: Z) (count_2: Z) (isprime: Z) (f2: Z) (f1: Z) (w: Z) (count: Z) (PreH1 : (count <> n_pre)) (PreH2 : ((w * w ) > f1)) (PreH3 : (0 <= count)) (PreH4 : (count < n_pre)) (PreH5 : (2 <= w)) (PreH6 : (2 <= f1)) (PreH7 : (f1 <= 144)) (PreH8 : (pf_state count f1 f2 )) (PreH9 : (w <= (f1 + 1 ))) (PreH10 : ((isprime = 0) -> (((((f1 <> 2) /\ (f1 <> 3)) /\ (f1 <> 5)) /\ (f1 <> 13)) /\ (f1 <> 89)))) (PreH11 : ((isprime <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < w)) -> ((f1 % ( k ) ) <> 0)))) (PreH12 : (count_2 < n_pre)) (PreH13 : (0 <= count_2)) (PreH14 : (count_2 < n_pre)) (PreH15 : (pf_state count_2 f2_2 (f1_2 + f2_2 ) )) (PreH16 : (problem_39_pre_z n_pre )) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 5)) (PreH19 : (isprime = 0)) ,
  TT && emp
|--
  “ (pf_state count f2 (f1 + f2 ) ) ”
  &&  emp
).

Definition prime_fib_entail_wit_4_2_split_goal_1 :=
forall (n_pre: Z) (f2_2: Z) (f1_2: Z) (count_2: Z) (isprime: Z) (f2: Z) (f1: Z) (w: Z) (count: Z) (PreH1 : (count <> n_pre)) (PreH2 : ((w * w ) > f1)) (PreH3 : (0 <= count)) (PreH4 : (count < n_pre)) (PreH5 : (2 <= w)) (PreH6 : (2 <= f1)) (PreH7 : (f1 <= 144)) (PreH8 : (pf_state count f1 f2 )) (PreH9 : (w <= (f1 + 1 ))) (PreH10 : ((isprime = 0) -> (((((f1 <> 2) /\ (f1 <> 3)) /\ (f1 <> 5)) /\ (f1 <> 13)) /\ (f1 <> 89)))) (PreH11 : ((isprime <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < w)) -> ((f1 % ( k ) ) <> 0)))) (PreH12 : (count_2 < n_pre)) (PreH13 : (0 <= count_2)) (PreH14 : (count_2 < n_pre)) (PreH15 : (pf_state count_2 f2_2 (f1_2 + f2_2 ) )) (PreH16 : (problem_39_pre_z n_pre )) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 5)) (PreH19 : (isprime = 0)) ,
  TT && emp
|--
  “ (pf_state count f2 (f1 + f2 ) ) ”
.

Definition prime_fib_entail_wit_4_3 :=
(
forall (n_pre: Z) (f2_2: Z) (f1_2: Z) (count_2: Z) (isprime: Z) (f2: Z) (f1: Z) (w: Z) (count: Z) (PreH1 : (count <> n_pre)) (PreH2 : ((f1 % ( w ) ) = 0)) (PreH3 : ((w * w ) <= f1)) (PreH4 : (0 <= count)) (PreH5 : (count < n_pre)) (PreH6 : (2 <= w)) (PreH7 : (2 <= f1)) (PreH8 : (f1 <= 144)) (PreH9 : (pf_state count f1 f2 )) (PreH10 : (w <= (f1 + 1 ))) (PreH11 : ((isprime = 0) -> (((((f1 <> 2) /\ (f1 <> 3)) /\ (f1 <> 5)) /\ (f1 <> 13)) /\ (f1 <> 89)))) (PreH12 : ((isprime <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < w)) -> ((f1 % ( k ) ) <> 0)))) (PreH13 : (count_2 < n_pre)) (PreH14 : (0 <= count_2)) (PreH15 : (count_2 < n_pre)) (PreH16 : (pf_state count_2 f2_2 (f1_2 + f2_2 ) )) (PreH17 : (problem_39_pre_z n_pre )) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 5)) ,
  ((( &( "m" ) )) # Int  |-> (f1_2 + f2_2 ))
|--
  “ (0 <= count) ”
  &&  “ (count < n_pre) ”
  &&  “ (pf_state count f2 (f1 + f2 ) ) ”
  &&  “ (problem_39_pre_z n_pre ) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 5) ”
  &&  ((( &( "m" ) )) # Int  |->_)
) \/
(
forall (n_pre: Z) (f2_2: Z) (f1_2: Z) (count_2: Z) (isprime: Z) (f2: Z) (f1: Z) (w: Z) (count: Z) (PreH1 : (count <> n_pre)) (PreH2 : ((f1 % ( w ) ) = 0)) (PreH3 : ((w * w ) <= f1)) (PreH4 : (0 <= count)) (PreH5 : (count < n_pre)) (PreH6 : (2 <= w)) (PreH7 : (2 <= f1)) (PreH8 : (f1 <= 144)) (PreH9 : (pf_state count f1 f2 )) (PreH10 : (w <= (f1 + 1 ))) (PreH11 : ((isprime = 0) -> (((((f1 <> 2) /\ (f1 <> 3)) /\ (f1 <> 5)) /\ (f1 <> 13)) /\ (f1 <> 89)))) (PreH12 : ((isprime <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < w)) -> ((f1 % ( k ) ) <> 0)))) (PreH13 : (count_2 < n_pre)) (PreH14 : (0 <= count_2)) (PreH15 : (count_2 < n_pre)) (PreH16 : (pf_state count_2 f2_2 (f1_2 + f2_2 ) )) (PreH17 : (problem_39_pre_z n_pre )) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 5)) ,
  TT && emp
|--
  “ (pf_state count f2 (f1 + f2 ) ) ”
  &&  emp
).

Definition prime_fib_entail_wit_4_3_split_goal_1 :=
forall (n_pre: Z) (f2_2: Z) (f1_2: Z) (count_2: Z) (isprime: Z) (f2: Z) (f1: Z) (w: Z) (count: Z) (PreH1 : (count <> n_pre)) (PreH2 : ((f1 % ( w ) ) = 0)) (PreH3 : ((w * w ) <= f1)) (PreH4 : (0 <= count)) (PreH5 : (count < n_pre)) (PreH6 : (2 <= w)) (PreH7 : (2 <= f1)) (PreH8 : (f1 <= 144)) (PreH9 : (pf_state count f1 f2 )) (PreH10 : (w <= (f1 + 1 ))) (PreH11 : ((isprime = 0) -> (((((f1 <> 2) /\ (f1 <> 3)) /\ (f1 <> 5)) /\ (f1 <> 13)) /\ (f1 <> 89)))) (PreH12 : ((isprime <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < w)) -> ((f1 % ( k ) ) <> 0)))) (PreH13 : (count_2 < n_pre)) (PreH14 : (0 <= count_2)) (PreH15 : (count_2 < n_pre)) (PreH16 : (pf_state count_2 f2_2 (f1_2 + f2_2 ) )) (PreH17 : (problem_39_pre_z n_pre )) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 5)) ,
  TT && emp
|--
  “ (pf_state count f2 (f1 + f2 ) ) ”
.

Definition prime_fib_return_wit_1 :=
(
forall (n_pre: Z) (f2: Z) (f1_2: Z) (count: Z) (isprime: Z) (f2_2: Z) (f1: Z) (w: Z) (count_2: Z) (PreH1 : ((count_2 + 1 ) = n_pre)) (PreH2 : ((w * w ) > f1)) (PreH3 : (0 <= count_2)) (PreH4 : (count_2 < n_pre)) (PreH5 : (2 <= w)) (PreH6 : (2 <= f1)) (PreH7 : (f1 <= 144)) (PreH8 : (pf_state count_2 f1 f2_2 )) (PreH9 : (w <= (f1 + 1 ))) (PreH10 : ((isprime = 0) -> (((((f1 <> 2) /\ (f1 <> 3)) /\ (f1 <> 5)) /\ (f1 <> 13)) /\ (f1 <> 89)))) (PreH11 : ((isprime <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < w)) -> ((f1 % ( k ) ) <> 0)))) (PreH12 : (count < n_pre)) (PreH13 : (0 <= count)) (PreH14 : (count < n_pre)) (PreH15 : (pf_state count f2 (f1_2 + f2 ) )) (PreH16 : (problem_39_pre_z n_pre )) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 5)) (PreH19 : (isprime <> 0)) ,
  TT && emp
|--
  “ (prime_fib_spec n_pre f1 ) ”
  &&  emp
) \/
(
forall (n_pre: Z) (f2: Z) (f1_2: Z) (count: Z) (isprime: Z) (f2_2: Z) (f1: Z) (w: Z) (count_2: Z) (PreH1 : ((count_2 + 1 ) = n_pre)) (PreH2 : ((w * w ) > f1)) (PreH3 : (0 <= count_2)) (PreH4 : (count_2 < n_pre)) (PreH5 : (2 <= w)) (PreH6 : (2 <= f1)) (PreH7 : (f1 <= 144)) (PreH8 : (pf_state count_2 f1 f2_2 )) (PreH9 : (w <= (f1 + 1 ))) (PreH10 : ((isprime = 0) -> (((((f1 <> 2) /\ (f1 <> 3)) /\ (f1 <> 5)) /\ (f1 <> 13)) /\ (f1 <> 89)))) (PreH11 : ((isprime <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < w)) -> ((f1 % ( k ) ) <> 0)))) (PreH12 : (count < n_pre)) (PreH13 : (0 <= count)) (PreH14 : (count < n_pre)) (PreH15 : (pf_state count f2 (f1_2 + f2 ) )) (PreH16 : (problem_39_pre_z n_pre )) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 5)) (PreH19 : (isprime <> 0)) ,
  TT && emp
|--
  “ (prime_fib_spec n_pre f1 ) ”
  &&  emp
).

Definition prime_fib_return_wit_1_split_goal_1 :=
forall (n_pre: Z) (f2: Z) (f1_2: Z) (count: Z) (isprime: Z) (f2_2: Z) (f1: Z) (w: Z) (count_2: Z) (PreH1 : ((count_2 + 1 ) = n_pre)) (PreH2 : ((w * w ) > f1)) (PreH3 : (0 <= count_2)) (PreH4 : (count_2 < n_pre)) (PreH5 : (2 <= w)) (PreH6 : (2 <= f1)) (PreH7 : (f1 <= 144)) (PreH8 : (pf_state count_2 f1 f2_2 )) (PreH9 : (w <= (f1 + 1 ))) (PreH10 : ((isprime = 0) -> (((((f1 <> 2) /\ (f1 <> 3)) /\ (f1 <> 5)) /\ (f1 <> 13)) /\ (f1 <> 89)))) (PreH11 : ((isprime <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < w)) -> ((f1 % ( k ) ) <> 0)))) (PreH12 : (count < n_pre)) (PreH13 : (0 <= count)) (PreH14 : (count < n_pre)) (PreH15 : (pf_state count f2 (f1_2 + f2 ) )) (PreH16 : (problem_39_pre_z n_pre )) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 5)) (PreH19 : (isprime <> 0)) ,
  TT && emp
|--
  “ (prime_fib_spec n_pre f1 ) ”
.

Module Type VC_Correct.


Axiom proof_of_prime_fib_safety_wit_1 : prime_fib_safety_wit_1.
Axiom proof_of_prime_fib_safety_wit_2 : prime_fib_safety_wit_2.
Axiom proof_of_prime_fib_safety_wit_3 : prime_fib_safety_wit_3.
Axiom proof_of_prime_fib_safety_wit_4 : prime_fib_safety_wit_4.
Axiom proof_of_prime_fib_safety_wit_5 : prime_fib_safety_wit_5.
Axiom proof_of_prime_fib_safety_wit_6 : prime_fib_safety_wit_6.
Axiom proof_of_prime_fib_safety_wit_7 : prime_fib_safety_wit_7.
Axiom proof_of_prime_fib_safety_wit_8 : prime_fib_safety_wit_8.
Axiom proof_of_prime_fib_safety_wit_9 : prime_fib_safety_wit_9.
Axiom proof_of_prime_fib_safety_wit_10 : prime_fib_safety_wit_10.
Axiom proof_of_prime_fib_safety_wit_11 : prime_fib_safety_wit_11.
Axiom proof_of_prime_fib_safety_wit_12 : prime_fib_safety_wit_12.
Axiom proof_of_prime_fib_safety_wit_13 : prime_fib_safety_wit_13.
Axiom proof_of_prime_fib_safety_wit_14 : prime_fib_safety_wit_14.
Axiom proof_of_prime_fib_safety_wit_15 : prime_fib_safety_wit_15.
Axiom proof_of_prime_fib_safety_wit_16 : prime_fib_safety_wit_16.
Axiom proof_of_prime_fib_entail_wit_1 : prime_fib_entail_wit_1.
Axiom proof_of_prime_fib_entail_wit_2 : prime_fib_entail_wit_2.
Axiom proof_of_prime_fib_entail_wit_3 : prime_fib_entail_wit_3.
Axiom proof_of_prime_fib_entail_wit_4_1 : prime_fib_entail_wit_4_1.
Axiom proof_of_prime_fib_entail_wit_4_2 : prime_fib_entail_wit_4_2.
Axiom proof_of_prime_fib_entail_wit_4_3 : prime_fib_entail_wit_4_3.
Axiom proof_of_prime_fib_return_wit_1 : prime_fib_return_wit_1.

End VC_Correct.
