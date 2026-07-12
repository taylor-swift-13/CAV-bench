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
Require Import p013_greatest_common_divisor.
Local Open Scope sac.

(*----- Function greatest_common_divisor -----*)

Definition greatest_common_divisor_safety_wit_1 :=
forall (b_pre: Z) (a_pre: Z) (a: Z) (b: Z) (PreH1 : ((Zgcd (a) (b)) = (Zgcd (a_pre) (b_pre)))) (PreH2 : (a > 0)) (PreH3 : (b > 0)) (PreH4 : (problem_13_pre a_pre b_pre )) (PreH5 : (a_pre > 0)) (PreH6 : (INT_MIN < a_pre)) (PreH7 : (a_pre <= INT_MAX)) (PreH8 : (INT_MIN < b_pre)) (PreH9 : (b_pre <= INT_MAX)) (PreH10 : (b_pre > 0)) ,
  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "m" ) )) # Int  |->_)
  **  ((( &( "out" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition greatest_common_divisor_safety_wit_2 :=
forall (b_pre: Z) (a_pre: Z) (a: Z) (b: Z) (PreH1 : (a < b)) (PreH2 : ((Zgcd (a) (b)) = (Zgcd (a_pre) (b_pre)))) (PreH3 : (a > 0)) (PreH4 : (b > 0)) (PreH5 : (problem_13_pre a_pre b_pre )) (PreH6 : (a_pre > 0)) (PreH7 : (INT_MIN < a_pre)) (PreH8 : (a_pre <= INT_MAX)) (PreH9 : (INT_MIN < b_pre)) (PreH10 : (b_pre <= INT_MAX)) (PreH11 : (b_pre > 0)) ,
  ((( &( "b" ) )) # Int  |-> a)
  **  ((( &( "a" ) )) # Int  |-> b)
  **  ((( &( "m" ) )) # Int  |-> a)
  **  ((( &( "out" ) )) # Int  |->_)
|--
  “ ((b <> (INT_MIN)) \/ (a <> (-1))) ”
  &&  “ (a <> 0) ”
.

Definition greatest_common_divisor_safety_wit_3 :=
forall (b_pre: Z) (a_pre: Z) (a: Z) (b: Z) (PreH1 : (a >= b)) (PreH2 : ((Zgcd (a) (b)) = (Zgcd (a_pre) (b_pre)))) (PreH3 : (a > 0)) (PreH4 : (b > 0)) (PreH5 : (problem_13_pre a_pre b_pre )) (PreH6 : (a_pre > 0)) (PreH7 : (INT_MIN < a_pre)) (PreH8 : (a_pre <= INT_MAX)) (PreH9 : (INT_MIN < b_pre)) (PreH10 : (b_pre <= INT_MAX)) (PreH11 : (b_pre > 0)) ,
  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "m" ) )) # Int  |->_)
  **  ((( &( "out" ) )) # Int  |->_)
|--
  “ ((a <> (INT_MIN)) \/ (b <> (-1))) ”
  &&  “ (b <> 0) ”
.

Definition greatest_common_divisor_safety_wit_4 :=
forall (b_pre: Z) (a_pre: Z) (a: Z) (b: Z) (PreH1 : (a < b)) (PreH2 : ((Zgcd (a) (b)) = (Zgcd (a_pre) (b_pre)))) (PreH3 : (a > 0)) (PreH4 : (b > 0)) (PreH5 : (problem_13_pre a_pre b_pre )) (PreH6 : (a_pre > 0)) (PreH7 : (INT_MIN < a_pre)) (PreH8 : (a_pre <= INT_MAX)) (PreH9 : (INT_MIN < b_pre)) (PreH10 : (b_pre <= INT_MAX)) (PreH11 : (b_pre > 0)) ,
  ((( &( "b" ) )) # Int  |-> a)
  **  ((( &( "a" ) )) # Int  |-> (b % ( a ) ))
  **  ((( &( "m" ) )) # Int  |-> a)
  **  ((( &( "out" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition greatest_common_divisor_safety_wit_5 :=
forall (b_pre: Z) (a_pre: Z) (a: Z) (b: Z) (PreH1 : (a >= b)) (PreH2 : ((Zgcd (a) (b)) = (Zgcd (a_pre) (b_pre)))) (PreH3 : (a > 0)) (PreH4 : (b > 0)) (PreH5 : (problem_13_pre a_pre b_pre )) (PreH6 : (a_pre > 0)) (PreH7 : (INT_MIN < a_pre)) (PreH8 : (a_pre <= INT_MAX)) (PreH9 : (INT_MIN < b_pre)) (PreH10 : (b_pre <= INT_MAX)) (PreH11 : (b_pre > 0)) ,
  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> (a % ( b ) ))
  **  ((( &( "m" ) )) # Int  |->_)
  **  ((( &( "out" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition greatest_common_divisor_entail_wit_1 :=
forall (b_pre: Z) (a_pre: Z) (PreH1 : (problem_13_pre a_pre b_pre )) (PreH2 : (a_pre > 0)) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) (PreH7 : (b_pre > 0)) ,
  TT && emp
|--
  “ ((Zgcd (a_pre) (b_pre)) = (Zgcd (a_pre) (b_pre))) ”
  &&  “ (a_pre > 0) ”
  &&  “ (b_pre > 0) ”
  &&  “ (problem_13_pre a_pre b_pre ) ”
  &&  “ (a_pre > 0) ”
  &&  “ (INT_MIN < a_pre) ”
  &&  “ (a_pre <= INT_MAX) ”
  &&  “ (INT_MIN < b_pre) ”
  &&  “ (b_pre <= INT_MAX) ”
  &&  “ (b_pre > 0) ”
  &&  emp
.

Definition greatest_common_divisor_entail_wit_2_1 :=
(
forall (b_pre: Z) (a_pre: Z) (a: Z) (b: Z) (PreH1 : ((b % ( a ) ) <> 0)) (PreH2 : (a < b)) (PreH3 : ((Zgcd (a) (b)) = (Zgcd (a_pre) (b_pre)))) (PreH4 : (a > 0)) (PreH5 : (b > 0)) (PreH6 : (problem_13_pre a_pre b_pre )) (PreH7 : (a_pre > 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) (PreH12 : (b_pre > 0)) ,
  ((( &( "m" ) )) # Int  |-> a)
|--
  “ ((Zgcd ((b % ( a ) )) (a)) = (Zgcd (a_pre) (b_pre))) ”
  &&  “ ((b % ( a ) ) > 0) ”
  &&  “ (a > 0) ”
  &&  “ (problem_13_pre a_pre b_pre ) ”
  &&  “ (a_pre > 0) ”
  &&  “ (INT_MIN < a_pre) ”
  &&  “ (a_pre <= INT_MAX) ”
  &&  “ (INT_MIN < b_pre) ”
  &&  “ (b_pre <= INT_MAX) ”
  &&  “ (b_pre > 0) ”
  &&  ((( &( "m" ) )) # Int  |->_)
) \/
(
forall (b_pre: Z) (a_pre: Z) (a: Z) (b: Z) (PreH1 : ((b % ( a ) ) <> 0)) (PreH2 : (a < b)) (PreH3 : ((Zgcd (a) (b)) = (Zgcd (a_pre) (b_pre)))) (PreH4 : (a > 0)) (PreH5 : (b > 0)) (PreH6 : (problem_13_pre a_pre b_pre )) (PreH7 : (a_pre > 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) (PreH12 : (b_pre > 0)) ,
  TT && emp
|--
  “ ((b % ( a ) ) > 0) ”
  &&  “ ((Zgcd ((b % ( a ) )) (a)) = (Zgcd (a_pre) (b_pre))) ”
  &&  emp
).

Definition greatest_common_divisor_entail_wit_2_1_split_goal_1 :=
forall (b_pre: Z) (a_pre: Z) (a: Z) (b: Z) (PreH1 : ((b % ( a ) ) <> 0)) (PreH2 : (a < b)) (PreH3 : ((Zgcd (a) (b)) = (Zgcd (a_pre) (b_pre)))) (PreH4 : (a > 0)) (PreH5 : (b > 0)) (PreH6 : (problem_13_pre a_pre b_pre )) (PreH7 : (a_pre > 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) (PreH12 : (b_pre > 0)) ,
  TT && emp
|--
  “ ((b % ( a ) ) > 0) ”
.

Definition greatest_common_divisor_entail_wit_2_1_split_goal_2 :=
forall (b_pre: Z) (a_pre: Z) (a: Z) (b: Z) (PreH1 : ((b % ( a ) ) <> 0)) (PreH2 : (a < b)) (PreH3 : ((Zgcd (a) (b)) = (Zgcd (a_pre) (b_pre)))) (PreH4 : (a > 0)) (PreH5 : (b > 0)) (PreH6 : (problem_13_pre a_pre b_pre )) (PreH7 : (a_pre > 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) (PreH12 : (b_pre > 0)) ,
  TT && emp
|--
  “ ((Zgcd ((b % ( a ) )) (a)) = (Zgcd (a_pre) (b_pre))) ”
.

Definition greatest_common_divisor_entail_wit_2_2 :=
(
forall (b_pre: Z) (a_pre: Z) (a: Z) (b: Z) (PreH1 : ((a % ( b ) ) <> 0)) (PreH2 : (a >= b)) (PreH3 : ((Zgcd (a) (b)) = (Zgcd (a_pre) (b_pre)))) (PreH4 : (a > 0)) (PreH5 : (b > 0)) (PreH6 : (problem_13_pre a_pre b_pre )) (PreH7 : (a_pre > 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) (PreH12 : (b_pre > 0)) ,
  TT && emp
|--
  “ ((Zgcd ((a % ( b ) )) (b)) = (Zgcd (a_pre) (b_pre))) ”
  &&  “ ((a % ( b ) ) > 0) ”
  &&  “ (b > 0) ”
  &&  “ (problem_13_pre a_pre b_pre ) ”
  &&  “ (a_pre > 0) ”
  &&  “ (INT_MIN < a_pre) ”
  &&  “ (a_pre <= INT_MAX) ”
  &&  “ (INT_MIN < b_pre) ”
  &&  “ (b_pre <= INT_MAX) ”
  &&  “ (b_pre > 0) ”
  &&  emp
) \/
(
forall (b_pre: Z) (a_pre: Z) (a: Z) (b: Z) (PreH1 : ((a % ( b ) ) <> 0)) (PreH2 : (a >= b)) (PreH3 : ((Zgcd (a) (b)) = (Zgcd (a_pre) (b_pre)))) (PreH4 : (a > 0)) (PreH5 : (b > 0)) (PreH6 : (problem_13_pre a_pre b_pre )) (PreH7 : (a_pre > 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) (PreH12 : (b_pre > 0)) ,
  TT && emp
|--
  “ ((a % ( b ) ) > 0) ”
  &&  “ ((Zgcd ((a % ( b ) )) (b)) = (Zgcd (a_pre) (b_pre))) ”
  &&  emp
).

Definition greatest_common_divisor_entail_wit_2_2_split_goal_1 :=
forall (b_pre: Z) (a_pre: Z) (a: Z) (b: Z) (PreH1 : ((a % ( b ) ) <> 0)) (PreH2 : (a >= b)) (PreH3 : ((Zgcd (a) (b)) = (Zgcd (a_pre) (b_pre)))) (PreH4 : (a > 0)) (PreH5 : (b > 0)) (PreH6 : (problem_13_pre a_pre b_pre )) (PreH7 : (a_pre > 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) (PreH12 : (b_pre > 0)) ,
  TT && emp
|--
  “ ((a % ( b ) ) > 0) ”
.

Definition greatest_common_divisor_entail_wit_2_2_split_goal_2 :=
forall (b_pre: Z) (a_pre: Z) (a: Z) (b: Z) (PreH1 : ((a % ( b ) ) <> 0)) (PreH2 : (a >= b)) (PreH3 : ((Zgcd (a) (b)) = (Zgcd (a_pre) (b_pre)))) (PreH4 : (a > 0)) (PreH5 : (b > 0)) (PreH6 : (problem_13_pre a_pre b_pre )) (PreH7 : (a_pre > 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) (PreH12 : (b_pre > 0)) ,
  TT && emp
|--
  “ ((Zgcd ((a % ( b ) )) (b)) = (Zgcd (a_pre) (b_pre))) ”
.

Definition greatest_common_divisor_return_wit_1 :=
(
forall (b_pre: Z) (a_pre: Z) (a: Z) (b: Z) (PreH1 : ((b % ( a ) ) = 0)) (PreH2 : (a < b)) (PreH3 : ((Zgcd (a) (b)) = (Zgcd (a_pre) (b_pre)))) (PreH4 : (a > 0)) (PreH5 : (b > 0)) (PreH6 : (problem_13_pre a_pre b_pre )) (PreH7 : (a_pre > 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) (PreH12 : (b_pre > 0)) ,
  TT && emp
|--
  “ (problem_13_spec a_pre b_pre a ) ”
  &&  emp
) \/
(
forall (b_pre: Z) (a_pre: Z) (a: Z) (b: Z) (PreH1 : ((b % ( a ) ) = 0)) (PreH2 : (a < b)) (PreH3 : ((Zgcd (a) (b)) = (Zgcd (a_pre) (b_pre)))) (PreH4 : (a > 0)) (PreH5 : (b > 0)) (PreH6 : (problem_13_pre a_pre b_pre )) (PreH7 : (a_pre > 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) (PreH12 : (b_pre > 0)) ,
  TT && emp
|--
  “ (problem_13_spec a_pre b_pre a ) ”
  &&  emp
).

Definition greatest_common_divisor_return_wit_1_split_goal_1 :=
forall (b_pre: Z) (a_pre: Z) (a: Z) (b: Z) (PreH1 : ((b % ( a ) ) = 0)) (PreH2 : (a < b)) (PreH3 : ((Zgcd (a) (b)) = (Zgcd (a_pre) (b_pre)))) (PreH4 : (a > 0)) (PreH5 : (b > 0)) (PreH6 : (problem_13_pre a_pre b_pre )) (PreH7 : (a_pre > 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) (PreH12 : (b_pre > 0)) ,
  TT && emp
|--
  “ (problem_13_spec a_pre b_pre a ) ”
.

Definition greatest_common_divisor_return_wit_2 :=
(
forall (b_pre: Z) (a_pre: Z) (a: Z) (b: Z) (PreH1 : ((a % ( b ) ) = 0)) (PreH2 : (a >= b)) (PreH3 : ((Zgcd (a) (b)) = (Zgcd (a_pre) (b_pre)))) (PreH4 : (a > 0)) (PreH5 : (b > 0)) (PreH6 : (problem_13_pre a_pre b_pre )) (PreH7 : (a_pre > 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) (PreH12 : (b_pre > 0)) ,
  TT && emp
|--
  “ (problem_13_spec a_pre b_pre b ) ”
  &&  emp
) \/
(
forall (b_pre: Z) (a_pre: Z) (a: Z) (b: Z) (PreH1 : ((a % ( b ) ) = 0)) (PreH2 : (a >= b)) (PreH3 : ((Zgcd (a) (b)) = (Zgcd (a_pre) (b_pre)))) (PreH4 : (a > 0)) (PreH5 : (b > 0)) (PreH6 : (problem_13_pre a_pre b_pre )) (PreH7 : (a_pre > 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) (PreH12 : (b_pre > 0)) ,
  TT && emp
|--
  “ (problem_13_spec a_pre b_pre b ) ”
  &&  emp
).

Definition greatest_common_divisor_return_wit_2_split_goal_1 :=
forall (b_pre: Z) (a_pre: Z) (a: Z) (b: Z) (PreH1 : ((a % ( b ) ) = 0)) (PreH2 : (a >= b)) (PreH3 : ((Zgcd (a) (b)) = (Zgcd (a_pre) (b_pre)))) (PreH4 : (a > 0)) (PreH5 : (b > 0)) (PreH6 : (problem_13_pre a_pre b_pre )) (PreH7 : (a_pre > 0)) (PreH8 : (INT_MIN < a_pre)) (PreH9 : (a_pre <= INT_MAX)) (PreH10 : (INT_MIN < b_pre)) (PreH11 : (b_pre <= INT_MAX)) (PreH12 : (b_pre > 0)) ,
  TT && emp
|--
  “ (problem_13_spec a_pre b_pre b ) ”
.

Module Type VC_Correct.


Axiom proof_of_greatest_common_divisor_safety_wit_1 : greatest_common_divisor_safety_wit_1.
Axiom proof_of_greatest_common_divisor_safety_wit_2 : greatest_common_divisor_safety_wit_2.
Axiom proof_of_greatest_common_divisor_safety_wit_3 : greatest_common_divisor_safety_wit_3.
Axiom proof_of_greatest_common_divisor_safety_wit_4 : greatest_common_divisor_safety_wit_4.
Axiom proof_of_greatest_common_divisor_safety_wit_5 : greatest_common_divisor_safety_wit_5.
Axiom proof_of_greatest_common_divisor_entail_wit_1 : greatest_common_divisor_entail_wit_1.
Axiom proof_of_greatest_common_divisor_entail_wit_2_1 : greatest_common_divisor_entail_wit_2_1.
Axiom proof_of_greatest_common_divisor_entail_wit_2_2 : greatest_common_divisor_entail_wit_2_2.
Axiom proof_of_greatest_common_divisor_return_wit_1 : greatest_common_divisor_return_wit_1.
Axiom proof_of_greatest_common_divisor_return_wit_2 : greatest_common_divisor_return_wit_2.

End VC_Correct.
