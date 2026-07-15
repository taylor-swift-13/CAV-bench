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
Require Import p059_largest_prime_factor.
Local Open Scope sac.

(*----- Function largest_prime_factor -----*)

Definition largest_prime_factor_safety_wit_1 := 
forall (n_pre: Z) (PreH1 : (problem_59_pre n_pre )) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition largest_prime_factor_safety_wit_2 := 
forall (n_pre: Z) (n: Z) (i: Z) (PreH1 : (2 <= i)) (PreH2 : (lpf_inv n_pre n i )) (PreH3 : (problem_59_pre n_pre )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ ((n <> (INT_MIN)) \/ (i <> (-1))) ” 
  &&  “ (i <> 0) ”
.

Definition largest_prime_factor_safety_wit_3 := 
forall (n_pre: Z) (n_2: Z) (i_2: Z) (n: Z) (i: Z) (PreH1 : (i >= 2)) (PreH2 : (lpf_while_inv n_pre n i )) (PreH3 : (i_2 <= (n_2 ÷ i_2 ))) (PreH4 : (2 <= i_2)) (PreH5 : (lpf_inv n_pre n_2 i_2 )) (PreH6 : (problem_59_pre n_pre )) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= INT_MAX)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ ((n <> (INT_MIN)) \/ (i <> (-1))) ” 
  &&  “ (i <> 0) ”
.

Definition largest_prime_factor_safety_wit_4 := 
forall (n_pre: Z) (n: Z) (i: Z) (n_2: Z) (i_2: Z) (PreH1 : (i_2 >= 2)) (PreH2 : (lpf_while_inv n_pre n_2 i_2 )) (PreH3 : (i <= (n ÷ i ))) (PreH4 : (2 <= i)) (PreH5 : (lpf_inv n_pre n i )) (PreH6 : (problem_59_pre n_pre )) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= INT_MAX)) ,
  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_2)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition largest_prime_factor_safety_wit_5 := 
(
forall (n_pre: Z) (n: Z) (i_2: Z) (n_2: Z) (i: Z) (PreH1 : ((n_2 % ( i ) ) <> 0)) (PreH2 : (i >= 2)) (PreH3 : (lpf_while_inv n_pre n_2 i )) (PreH4 : (i_2 <= (n ÷ i_2 ))) (PreH5 : (2 <= i_2)) (PreH6 : (lpf_inv n_pre n i_2 )) (PreH7 : (problem_59_pre n_pre )) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_2)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
) \/
(
forall (n_pre: Z) (n: Z) (i_2: Z) (n_2: Z) (i: Z) (PreH1 : ((n_2 % ( i ) ) <> 0)) (PreH2 : (i >= 2)) (PreH3 : (lpf_while_inv n_pre n_2 i )) (PreH4 : (i_2 <= (n ÷ i_2 ))) (PreH5 : (2 <= i_2)) (PreH6 : (lpf_inv n_pre n i_2 )) (PreH7 : (problem_59_pre n_pre )) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_2)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
).

Definition largest_prime_factor_safety_wit_5_split_goal_1 := 
forall (n_pre: Z) (n: Z) (i_2: Z) (n_2: Z) (i: Z) (PreH1 : ((n_2 % ( i ) ) <> 0)) (PreH2 : (i >= 2)) (PreH3 : (lpf_while_inv n_pre n_2 i )) (PreH4 : (i_2 <= (n ÷ i_2 ))) (PreH5 : (2 <= i_2)) (PreH6 : (lpf_inv n_pre n i_2 )) (PreH7 : (problem_59_pre n_pre )) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_2)
|--
  “ ((i + 1 ) <= INT_MAX) ”
.

Definition largest_prime_factor_safety_wit_5_split_goal_2 := 
forall (n_pre: Z) (n: Z) (i_2: Z) (n_2: Z) (i: Z) (PreH1 : ((n_2 % ( i ) ) <> 0)) (PreH2 : (i >= 2)) (PreH3 : (lpf_while_inv n_pre n_2 i )) (PreH4 : (i_2 <= (n ÷ i_2 ))) (PreH5 : (2 <= i_2)) (PreH6 : (lpf_inv n_pre n i_2 )) (PreH7 : (problem_59_pre n_pre )) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_2)
|--
  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition largest_prime_factor_safety_wit_6 := 
(
forall (n_pre: Z) (n: Z) (i_2: Z) (n_2: Z) (i: Z) (PreH1 : (n_2 <= i)) (PreH2 : ((n_2 % ( i ) ) = 0)) (PreH3 : (i >= 2)) (PreH4 : (lpf_while_inv n_pre n_2 i )) (PreH5 : (i_2 <= (n ÷ i_2 ))) (PreH6 : (2 <= i_2)) (PreH7 : (lpf_inv n_pre n i_2 )) (PreH8 : (problem_59_pre n_pre )) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_2)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
) \/
(
forall (n_pre: Z) (n: Z) (i_2: Z) (n_2: Z) (i: Z) (PreH1 : (n_2 <= i)) (PreH2 : ((n_2 % ( i ) ) = 0)) (PreH3 : (i >= 2)) (PreH4 : (lpf_while_inv n_pre n_2 i )) (PreH5 : (i_2 <= (n ÷ i_2 ))) (PreH6 : (2 <= i_2)) (PreH7 : (lpf_inv n_pre n i_2 )) (PreH8 : (problem_59_pre n_pre )) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_2)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
).

Definition largest_prime_factor_safety_wit_6_split_goal_1 := 
forall (n_pre: Z) (n: Z) (i_2: Z) (n_2: Z) (i: Z) (PreH1 : (n_2 <= i)) (PreH2 : ((n_2 % ( i ) ) = 0)) (PreH3 : (i >= 2)) (PreH4 : (lpf_while_inv n_pre n_2 i )) (PreH5 : (i_2 <= (n ÷ i_2 ))) (PreH6 : (2 <= i_2)) (PreH7 : (lpf_inv n_pre n i_2 )) (PreH8 : (problem_59_pre n_pre )) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_2)
|--
  “ ((i + 1 ) <= INT_MAX) ”
.

Definition largest_prime_factor_safety_wit_6_split_goal_2 := 
forall (n_pre: Z) (n: Z) (i_2: Z) (n_2: Z) (i: Z) (PreH1 : (n_2 <= i)) (PreH2 : ((n_2 % ( i ) ) = 0)) (PreH3 : (i >= 2)) (PreH4 : (lpf_while_inv n_pre n_2 i )) (PreH5 : (i_2 <= (n ÷ i_2 ))) (PreH6 : (2 <= i_2)) (PreH7 : (lpf_inv n_pre n i_2 )) (PreH8 : (problem_59_pre n_pre )) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_2)
|--
  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition largest_prime_factor_safety_wit_7 := 
forall (n_pre: Z) (n_2: Z) (i_2: Z) (n: Z) (i: Z) (PreH1 : (n > i)) (PreH2 : ((n % ( i ) ) = 0)) (PreH3 : (i >= 2)) (PreH4 : (lpf_while_inv n_pre n i )) (PreH5 : (i_2 <= (n_2 ÷ i_2 ))) (PreH6 : (2 <= i_2)) (PreH7 : (lpf_inv n_pre n_2 i_2 )) (PreH8 : (problem_59_pre n_pre )) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ ((n <> (INT_MIN)) \/ (i <> (-1))) ” 
  &&  “ (i <> 0) ”
.

Definition largest_prime_factor_entail_wit_1 := 
(
forall (n_pre: Z) (PreH1 : (problem_59_pre n_pre )) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (2 <= 2) ” 
  &&  “ (lpf_inv n_pre n_pre 2 ) ” 
  &&  “ (problem_59_pre n_pre ) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  emp
) \/
(
forall (n_pre: Z) (PreH1 : (problem_59_pre n_pre )) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (lpf_inv n_pre n_pre 2 ) ”
  &&  emp
).

Definition largest_prime_factor_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (PreH1 : (problem_59_pre n_pre )) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= INT_MAX)) ,
  (lpf_inv n_pre n_pre 2 )
.

Definition largest_prime_factor_entail_wit_2 := 
(
forall (n_pre: Z) (n: Z) (i: Z) (PreH1 : (i <= (n ÷ i ))) (PreH2 : (2 <= i)) (PreH3 : (lpf_inv n_pre n i )) (PreH4 : (problem_59_pre n_pre )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (i >= 2) ” 
  &&  “ (lpf_while_inv n_pre n i ) ” 
  &&  “ (i <= (n ÷ i )) ” 
  &&  “ (2 <= i) ” 
  &&  “ (lpf_inv n_pre n i ) ” 
  &&  “ (problem_59_pre n_pre ) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  emp
) \/
(
forall (n_pre: Z) (n: Z) (i: Z) (PreH1 : (i <= (n ÷ i ))) (PreH2 : (2 <= i)) (PreH3 : (lpf_inv n_pre n i )) (PreH4 : (problem_59_pre n_pre )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (lpf_while_inv n_pre n i ) ”
  &&  emp
).

Definition largest_prime_factor_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (n: Z) (i: Z) (PreH1 : (i <= (n ÷ i ))) (PreH2 : (2 <= i)) (PreH3 : (lpf_inv n_pre n i )) (PreH4 : (problem_59_pre n_pre )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) ,
  (lpf_while_inv n_pre n i )
.

Definition largest_prime_factor_entail_wit_3_1 := 
(
forall (n_pre: Z) (n_2: Z) (i_2: Z) (n: Z) (i: Z) (PreH1 : ((n % ( i ) ) <> 0)) (PreH2 : (i >= 2)) (PreH3 : (lpf_while_inv n_pre n i )) (PreH4 : (i_2 <= (n_2 ÷ i_2 ))) (PreH5 : (2 <= i_2)) (PreH6 : (lpf_inv n_pre n_2 i_2 )) (PreH7 : (problem_59_pre n_pre )) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (2 <= (i + 1 )) ” 
  &&  “ (lpf_inv n_pre n (i + 1 ) ) ” 
  &&  “ (problem_59_pre n_pre ) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  emp
) \/
(
forall (n_pre: Z) (n_2: Z) (i_2: Z) (n: Z) (i: Z) (PreH1 : ((n % ( i ) ) <> 0)) (PreH2 : (i >= 2)) (PreH3 : (lpf_while_inv n_pre n i )) (PreH4 : (i_2 <= (n_2 ÷ i_2 ))) (PreH5 : (2 <= i_2)) (PreH6 : (lpf_inv n_pre n_2 i_2 )) (PreH7 : (problem_59_pre n_pre )) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (lpf_inv n_pre n (i + 1 ) ) ”
  &&  emp
).

Definition largest_prime_factor_entail_wit_3_1_split_goal_1 := 
forall (n_pre: Z) (n_2: Z) (i_2: Z) (n: Z) (i: Z) (PreH1 : ((n % ( i ) ) <> 0)) (PreH2 : (i >= 2)) (PreH3 : (lpf_while_inv n_pre n i )) (PreH4 : (i_2 <= (n_2 ÷ i_2 ))) (PreH5 : (2 <= i_2)) (PreH6 : (lpf_inv n_pre n_2 i_2 )) (PreH7 : (problem_59_pre n_pre )) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) ,
  (lpf_inv n_pre n (i + 1 ) )
.

Definition largest_prime_factor_entail_wit_3_2 := 
(
forall (n_pre: Z) (n_2: Z) (i_2: Z) (n: Z) (i: Z) (PreH1 : (n <= i)) (PreH2 : ((n % ( i ) ) = 0)) (PreH3 : (i >= 2)) (PreH4 : (lpf_while_inv n_pre n i )) (PreH5 : (i_2 <= (n_2 ÷ i_2 ))) (PreH6 : (2 <= i_2)) (PreH7 : (lpf_inv n_pre n_2 i_2 )) (PreH8 : (problem_59_pre n_pre )) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (2 <= (i + 1 )) ” 
  &&  “ (lpf_inv n_pre n (i + 1 ) ) ” 
  &&  “ (problem_59_pre n_pre ) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  emp
) \/
(
forall (n_pre: Z) (n_2: Z) (i_2: Z) (n: Z) (i: Z) (PreH1 : (n <= i)) (PreH2 : ((n % ( i ) ) = 0)) (PreH3 : (i >= 2)) (PreH4 : (lpf_while_inv n_pre n i )) (PreH5 : (i_2 <= (n_2 ÷ i_2 ))) (PreH6 : (2 <= i_2)) (PreH7 : (lpf_inv n_pre n_2 i_2 )) (PreH8 : (problem_59_pre n_pre )) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (lpf_inv n_pre n (i + 1 ) ) ”
  &&  emp
).

Definition largest_prime_factor_entail_wit_3_2_split_goal_1 := 
forall (n_pre: Z) (n_2: Z) (i_2: Z) (n: Z) (i: Z) (PreH1 : (n <= i)) (PreH2 : ((n % ( i ) ) = 0)) (PreH3 : (i >= 2)) (PreH4 : (lpf_while_inv n_pre n i )) (PreH5 : (i_2 <= (n_2 ÷ i_2 ))) (PreH6 : (2 <= i_2)) (PreH7 : (lpf_inv n_pre n_2 i_2 )) (PreH8 : (problem_59_pre n_pre )) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) ,
  (lpf_inv n_pre n (i + 1 ) )
.

Definition largest_prime_factor_entail_wit_4 := 
(
forall (n_pre: Z) (n: Z) (i: Z) (n_2: Z) (i_2: Z) (PreH1 : (n_2 > i_2)) (PreH2 : ((n_2 % ( i_2 ) ) = 0)) (PreH3 : (i_2 >= 2)) (PreH4 : (lpf_while_inv n_pre n_2 i_2 )) (PreH5 : (i <= (n ÷ i ))) (PreH6 : (2 <= i)) (PreH7 : (lpf_inv n_pre n i )) (PreH8 : (problem_59_pre n_pre )) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (i_2 >= 2) ” 
  &&  “ (lpf_while_inv n_pre (n_2 ÷ i_2 ) i_2 ) ” 
  &&  “ (i <= (n ÷ i )) ” 
  &&  “ (2 <= i) ” 
  &&  “ (lpf_inv n_pre n i ) ” 
  &&  “ (problem_59_pre n_pre ) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  emp
) \/
(
forall (n_pre: Z) (n: Z) (i: Z) (n_2: Z) (i_2: Z) (PreH1 : (n_2 > i_2)) (PreH2 : ((n_2 % ( i_2 ) ) = 0)) (PreH3 : (i_2 >= 2)) (PreH4 : (lpf_while_inv n_pre n_2 i_2 )) (PreH5 : (i <= (n ÷ i ))) (PreH6 : (2 <= i)) (PreH7 : (lpf_inv n_pre n i )) (PreH8 : (problem_59_pre n_pre )) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (lpf_while_inv n_pre (n_2 ÷ i_2 ) i_2 ) ”
  &&  emp
).

Definition largest_prime_factor_entail_wit_4_split_goal_1 := 
forall (n_pre: Z) (n: Z) (i: Z) (n_2: Z) (i_2: Z) (PreH1 : (n_2 > i_2)) (PreH2 : ((n_2 % ( i_2 ) ) = 0)) (PreH3 : (i_2 >= 2)) (PreH4 : (lpf_while_inv n_pre n_2 i_2 )) (PreH5 : (i <= (n ÷ i ))) (PreH6 : (2 <= i)) (PreH7 : (lpf_inv n_pre n i )) (PreH8 : (problem_59_pre n_pre )) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= INT_MAX)) ,
  (lpf_while_inv n_pre (n_2 ÷ i_2 ) i_2 )
.

Definition largest_prime_factor_return_wit_1 := 
(
forall (n_pre: Z) (n: Z) (i: Z) (PreH1 : (i > (n ÷ i ))) (PreH2 : (2 <= i)) (PreH3 : (lpf_inv n_pre n i )) (PreH4 : (problem_59_pre n_pre )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (problem_59_spec n_pre n ) ”
  &&  emp
) \/
(
forall (n_pre: Z) (n: Z) (i: Z) (PreH1 : (i > (n ÷ i ))) (PreH2 : (2 <= i)) (PreH3 : (lpf_inv n_pre n i )) (PreH4 : (problem_59_pre n_pre )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (problem_59_spec n_pre n ) ”
  &&  emp
).

Definition largest_prime_factor_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (n: Z) (i: Z) (PreH1 : (i > (n ÷ i ))) (PreH2 : (2 <= i)) (PreH3 : (lpf_inv n_pre n i )) (PreH4 : (problem_59_pre n_pre )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) ,
  (problem_59_spec n_pre n )
.

Module Type VC_Correct.


Axiom proof_of_largest_prime_factor_safety_wit_1 : largest_prime_factor_safety_wit_1.
Axiom proof_of_largest_prime_factor_safety_wit_2 : largest_prime_factor_safety_wit_2.
Axiom proof_of_largest_prime_factor_safety_wit_3 : largest_prime_factor_safety_wit_3.
Axiom proof_of_largest_prime_factor_safety_wit_4 : largest_prime_factor_safety_wit_4.
Axiom proof_of_largest_prime_factor_safety_wit_5 : largest_prime_factor_safety_wit_5.
Axiom proof_of_largest_prime_factor_safety_wit_6 : largest_prime_factor_safety_wit_6.
Axiom proof_of_largest_prime_factor_safety_wit_7 : largest_prime_factor_safety_wit_7.
Axiom proof_of_largest_prime_factor_entail_wit_1 : largest_prime_factor_entail_wit_1.
Axiom proof_of_largest_prime_factor_entail_wit_2 : largest_prime_factor_entail_wit_2.
Axiom proof_of_largest_prime_factor_entail_wit_3_1 : largest_prime_factor_entail_wit_3_1.
Axiom proof_of_largest_prime_factor_entail_wit_3_2 : largest_prime_factor_entail_wit_3_2.
Axiom proof_of_largest_prime_factor_entail_wit_4 : largest_prime_factor_entail_wit_4.
Axiom proof_of_largest_prime_factor_return_wit_1 : largest_prime_factor_return_wit_1.

End VC_Correct.
