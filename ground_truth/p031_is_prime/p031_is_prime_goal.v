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
Require Import p031_is_prime.
Local Open Scope sac.

(*----- Function is_prime -----*)

Definition is_prime_safety_wit_1 :=
forall (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 2147395600)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition is_prime_safety_wit_2 :=
forall (n_pre: Z) (PreH1 : (n_pre < 2)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 2147395600)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_prime_safety_wit_3 :=
forall (n_pre: Z) (PreH1 : (n_pre >= 2)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 2147395600)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition is_prime_safety_wit_4 :=
(
forall (n_pre: Z) (i: Z) (PreH1 : (2 <= i)) (PreH2 : (i <= 46340)) (PreH3 : (((i - 1 ) * (i - 1 ) ) <= n_pre)) (PreH4 : forall (k: Z) , (((2 <= k) /\ (k < i)) -> ((n_pre % ( k ) ) <> 0))) (PreH5 : (n_pre >= 2)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 2147395600)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((i * i ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i * i )) ”
) \/
(
forall (n_pre: Z) (i: Z) (PreH1 : (2 <= i)) (PreH2 : (i <= 46340)) (PreH3 : (((i - 1 ) * (i - 1 ) ) <= n_pre)) (PreH4 : forall (k: Z) , (((2 <= k) /\ (k < i)) -> ((n_pre % ( k ) ) <> 0))) (PreH5 : (n_pre >= 2)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 2147395600)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((i * i ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i * i )) ”
).

Definition is_prime_safety_wit_4_split_goal_1 :=
forall (n_pre: Z) (i: Z) (PreH1 : (2 <= i)) (PreH2 : (i <= 46340)) (PreH3 : (((i - 1 ) * (i - 1 ) ) <= n_pre)) (PreH4 : forall (k: Z) , (((2 <= k) /\ (k < i)) -> ((n_pre % ( k ) ) <> 0))) (PreH5 : (n_pre >= 2)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 2147395600)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((i * i ) <= INT_MAX) ”
.

Definition is_prime_safety_wit_4_split_goal_2 :=
forall (n_pre: Z) (i: Z) (PreH1 : (2 <= i)) (PreH2 : (i <= 46340)) (PreH3 : (((i - 1 ) * (i - 1 ) ) <= n_pre)) (PreH4 : forall (k: Z) , (((2 <= k) /\ (k < i)) -> ((n_pre % ( k ) ) <> 0))) (PreH5 : (n_pre >= 2)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 2147395600)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((INT_MIN) <= (i * i )) ”
.

Definition is_prime_safety_wit_5 :=
forall (n_pre: Z) (i: Z) (PreH1 : ((i * i ) <= n_pre)) (PreH2 : (2 <= i)) (PreH3 : (i <= 46340)) (PreH4 : (((i - 1 ) * (i - 1 ) ) <= n_pre)) (PreH5 : forall (k: Z) , (((2 <= k) /\ (k < i)) -> ((n_pre % ( k ) ) <> 0))) (PreH6 : (n_pre >= 2)) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 2147395600)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((n_pre <> (INT_MIN)) \/ (i <> (-1))) ”
  &&  “ (i <> 0) ”
.

Definition is_prime_safety_wit_6 :=
forall (n_pre: Z) (i: Z) (PreH1 : ((i * i ) <= n_pre)) (PreH2 : (2 <= i)) (PreH3 : (i <= 46340)) (PreH4 : (((i - 1 ) * (i - 1 ) ) <= n_pre)) (PreH5 : forall (k: Z) , (((2 <= k) /\ (k < i)) -> ((n_pre % ( k ) ) <> 0))) (PreH6 : (n_pre >= 2)) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 2147395600)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_prime_safety_wit_7 :=
forall (n_pre: Z) (i: Z) (PreH1 : ((n_pre % ( i ) ) = 0)) (PreH2 : ((i * i ) <= n_pre)) (PreH3 : (2 <= i)) (PreH4 : (i <= 46340)) (PreH5 : (((i - 1 ) * (i - 1 ) ) <= n_pre)) (PreH6 : forall (k: Z) , (((2 <= k) /\ (k < i)) -> ((n_pre % ( k ) ) <> 0))) (PreH7 : (n_pre >= 2)) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 2147395600)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_prime_safety_wit_8 :=
forall (n_pre: Z) (i: Z) (PreH1 : ((i * i ) > n_pre)) (PreH2 : (2 <= i)) (PreH3 : (i <= 46340)) (PreH4 : (((i - 1 ) * (i - 1 ) ) <= n_pre)) (PreH5 : forall (k: Z) , (((2 <= k) /\ (k < i)) -> ((n_pre % ( k ) ) <> 0))) (PreH6 : (n_pre >= 2)) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 2147395600)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_prime_safety_wit_9 :=
forall (n_pre: Z) (i: Z) (PreH1 : ((n_pre % ( i ) ) <> 0)) (PreH2 : ((i * i ) <= n_pre)) (PreH3 : (2 <= i)) (PreH4 : (i <= 46340)) (PreH5 : (((i - 1 ) * (i - 1 ) ) <= n_pre)) (PreH6 : forall (k: Z) , (((2 <= k) /\ (k < i)) -> ((n_pre % ( k ) ) <> 0))) (PreH7 : (n_pre >= 2)) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 2147395600)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition is_prime_entail_wit_1 :=
forall (n_pre: Z) (PreH1 : (n_pre >= 2)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 2147395600)) ,
  TT && emp
|--
  “ (2 <= 2) ”
  &&  “ (2 <= 46340) ”
  &&  “ (((2 - 1 ) * (2 - 1 ) ) <= n_pre) ”
  &&  “ forall (k: Z) , (((2 <= k) /\ (k < 2)) -> ((n_pre % ( k ) ) <> 0)) ”
  &&  “ (n_pre >= 2) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 2147395600) ”
  &&  emp
.

Definition is_prime_entail_wit_2 :=
(
forall (n_pre: Z) (i: Z) (PreH1 : ((n_pre % ( i ) ) <> 0)) (PreH2 : ((i * i ) <= n_pre)) (PreH3 : (2 <= i)) (PreH4 : (i <= 46340)) (PreH5 : (((i - 1 ) * (i - 1 ) ) <= n_pre)) (PreH6 : forall (k: Z) , (((2 <= k) /\ (k < i)) -> ((n_pre % ( k ) ) <> 0))) (PreH7 : (n_pre >= 2)) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 2147395600)) ,
  TT && emp
|--
  “ (2 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= 46340) ”
  &&  “ ((((i + 1 ) - 1 ) * ((i + 1 ) - 1 ) ) <= n_pre) ”
  &&  “ forall (k: Z) , (((2 <= k) /\ (k < (i + 1 ))) -> ((n_pre % ( k ) ) <> 0)) ”
  &&  “ (n_pre >= 2) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= 2147395600) ”
  &&  emp
) \/
(
forall (n_pre: Z) (i: Z) (PreH1 : ((n_pre % ( i ) ) <> 0)) (PreH2 : ((i * i ) <= n_pre)) (PreH3 : (2 <= i)) (PreH4 : (i <= 46340)) (PreH5 : (((i - 1 ) * (i - 1 ) ) <= n_pre)) (PreH6 : forall (k: Z) , (((2 <= k) /\ (k < i)) -> ((n_pre % ( k ) ) <> 0))) (PreH7 : (n_pre >= 2)) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 2147395600)) ,
  TT && emp
|--
  “ (((n_pre % ( 2 ) ) <> 0) /\ ((n_pre % ( ((i + 1 ) - 1 ) ) ) <> 0)) ”
  &&  “ ((((i + 1 ) - 1 ) * ((i + 1 ) - 1 ) ) <= n_pre) ”
  &&  “ ((i + 1 ) <= 46340) ”
  &&  emp
).

Definition is_prime_entail_wit_2_split_goal_1 :=
forall (n_pre: Z) (i: Z) (PreH1 : ((n_pre % ( i ) ) <> 0)) (PreH2 : ((i * i ) <= n_pre)) (PreH3 : (2 <= i)) (PreH4 : (i <= 46340)) (PreH5 : (((i - 1 ) * (i - 1 ) ) <= n_pre)) (PreH6 : forall (k: Z) , (((2 <= k) /\ (k < i)) -> ((n_pre % ( k ) ) <> 0))) (PreH7 : (n_pre >= 2)) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 2147395600)) ,
  TT && emp
|--
  “ (((n_pre % ( 2 ) ) <> 0) /\ ((n_pre % ( ((i + 1 ) - 1 ) ) ) <> 0)) ”
.

Definition is_prime_entail_wit_2_split_goal_2 :=
forall (n_pre: Z) (i: Z) (PreH1 : ((n_pre % ( i ) ) <> 0)) (PreH2 : ((i * i ) <= n_pre)) (PreH3 : (2 <= i)) (PreH4 : (i <= 46340)) (PreH5 : (((i - 1 ) * (i - 1 ) ) <= n_pre)) (PreH6 : forall (k: Z) , (((2 <= k) /\ (k < i)) -> ((n_pre % ( k ) ) <> 0))) (PreH7 : (n_pre >= 2)) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 2147395600)) ,
  TT && emp
|--
  “ ((((i + 1 ) - 1 ) * ((i + 1 ) - 1 ) ) <= n_pre) ”
.

Definition is_prime_entail_wit_2_split_goal_3 :=
forall (n_pre: Z) (i: Z) (PreH1 : ((n_pre % ( i ) ) <> 0)) (PreH2 : ((i * i ) <= n_pre)) (PreH3 : (2 <= i)) (PreH4 : (i <= 46340)) (PreH5 : (((i - 1 ) * (i - 1 ) ) <= n_pre)) (PreH6 : forall (k: Z) , (((2 <= k) /\ (k < i)) -> ((n_pre % ( k ) ) <> 0))) (PreH7 : (n_pre >= 2)) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 2147395600)) ,
  TT && emp
|--
  “ ((i + 1 ) <= 46340) ”
.

Definition is_prime_return_wit_1 :=
(
forall (n_pre: Z) (i: Z) (PreH1 : ((i * i ) > n_pre)) (PreH2 : (2 <= i)) (PreH3 : (i <= 46340)) (PreH4 : (((i - 1 ) * (i - 1 ) ) <= n_pre)) (PreH5 : forall (k: Z) , (((2 <= k) /\ (k < i)) -> ((n_pre % ( k ) ) <> 0))) (PreH6 : (n_pre >= 2)) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 2147395600)) ,
  TT && emp
|--
  “ (problem_31_spec_z n_pre 1 ) ”
  &&  emp
) \/
(
forall (n_pre: Z) (i: Z) (PreH1 : ((i * i ) > n_pre)) (PreH2 : (2 <= i)) (PreH3 : (i <= 46340)) (PreH4 : (((i - 1 ) * (i - 1 ) ) <= n_pre)) (PreH5 : forall (k: Z) , (((2 <= k) /\ (k < i)) -> ((n_pre % ( k ) ) <> 0))) (PreH6 : (n_pre >= 2)) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 2147395600)) ,
  TT && emp
|--
  “ (problem_31_spec_z n_pre 1 ) ”
  &&  emp
).

Definition is_prime_return_wit_1_split_goal_1 :=
forall (n_pre: Z) (i: Z) (PreH1 : ((i * i ) > n_pre)) (PreH2 : (2 <= i)) (PreH3 : (i <= 46340)) (PreH4 : (((i - 1 ) * (i - 1 ) ) <= n_pre)) (PreH5 : forall (k: Z) , (((2 <= k) /\ (k < i)) -> ((n_pre % ( k ) ) <> 0))) (PreH6 : (n_pre >= 2)) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 2147395600)) ,
  TT && emp
|--
  “ (problem_31_spec_z n_pre 1 ) ”
.

Definition is_prime_return_wit_2 :=
(
forall (n_pre: Z) (i: Z) (PreH1 : ((n_pre % ( i ) ) = 0)) (PreH2 : ((i * i ) <= n_pre)) (PreH3 : (2 <= i)) (PreH4 : (i <= 46340)) (PreH5 : (((i - 1 ) * (i - 1 ) ) <= n_pre)) (PreH6 : forall (k: Z) , (((2 <= k) /\ (k < i)) -> ((n_pre % ( k ) ) <> 0))) (PreH7 : (n_pre >= 2)) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 2147395600)) ,
  TT && emp
|--
  “ (problem_31_spec_z n_pre 0 ) ”
  &&  emp
) \/
(
forall (n_pre: Z) (i: Z) (PreH1 : ((n_pre % ( i ) ) = 0)) (PreH2 : ((i * i ) <= n_pre)) (PreH3 : (2 <= i)) (PreH4 : (i <= 46340)) (PreH5 : (((i - 1 ) * (i - 1 ) ) <= n_pre)) (PreH6 : forall (k: Z) , (((2 <= k) /\ (k < i)) -> ((n_pre % ( k ) ) <> 0))) (PreH7 : (n_pre >= 2)) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 2147395600)) ,
  TT && emp
|--
  “ (problem_31_spec_z n_pre 0 ) ”
  &&  emp
).

Definition is_prime_return_wit_2_split_goal_1 :=
forall (n_pre: Z) (i: Z) (PreH1 : ((n_pre % ( i ) ) = 0)) (PreH2 : ((i * i ) <= n_pre)) (PreH3 : (2 <= i)) (PreH4 : (i <= 46340)) (PreH5 : (((i - 1 ) * (i - 1 ) ) <= n_pre)) (PreH6 : forall (k: Z) , (((2 <= k) /\ (k < i)) -> ((n_pre % ( k ) ) <> 0))) (PreH7 : (n_pre >= 2)) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 2147395600)) ,
  TT && emp
|--
  “ (problem_31_spec_z n_pre 0 ) ”
.

Definition is_prime_return_wit_3 :=
(
forall (n_pre: Z) (PreH1 : (n_pre < 2)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 2147395600)) ,
  TT && emp
|--
  “ (problem_31_spec_z n_pre 0 ) ”
  &&  emp
) \/
(
forall (n_pre: Z) (PreH1 : (n_pre < 2)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 2147395600)) ,
  TT && emp
|--
  “ (problem_31_spec_z n_pre 0 ) ”
  &&  emp
).

Definition is_prime_return_wit_3_split_goal_1 :=
forall (n_pre: Z) (PreH1 : (n_pre < 2)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 2147395600)) ,
  TT && emp
|--
  “ (problem_31_spec_z n_pre 0 ) ”
.

Module Type VC_Correct.


Axiom proof_of_is_prime_safety_wit_1 : is_prime_safety_wit_1.
Axiom proof_of_is_prime_safety_wit_2 : is_prime_safety_wit_2.
Axiom proof_of_is_prime_safety_wit_3 : is_prime_safety_wit_3.
Axiom proof_of_is_prime_safety_wit_4 : is_prime_safety_wit_4.
Axiom proof_of_is_prime_safety_wit_5 : is_prime_safety_wit_5.
Axiom proof_of_is_prime_safety_wit_6 : is_prime_safety_wit_6.
Axiom proof_of_is_prime_safety_wit_7 : is_prime_safety_wit_7.
Axiom proof_of_is_prime_safety_wit_8 : is_prime_safety_wit_8.
Axiom proof_of_is_prime_safety_wit_9 : is_prime_safety_wit_9.
Axiom proof_of_is_prime_entail_wit_1 : is_prime_entail_wit_1.
Axiom proof_of_is_prime_entail_wit_2 : is_prime_entail_wit_2.
Axiom proof_of_is_prime_return_wit_1 : is_prime_return_wit_1.
Axiom proof_of_is_prime_return_wit_2 : is_prime_return_wit_2.
Axiom proof_of_is_prime_return_wit_3 : is_prime_return_wit_3.

End VC_Correct.
