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
Require Import p083_starts_one_ends.
Local Open Scope sac.

(*----- Function starts_one_ends -----*)

Definition starts_one_ends_safety_wit_1 := 
forall (n_pre: Z) (PreH1 : (problem_83_pre_z n_pre )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 9)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition starts_one_ends_safety_wit_2 := 
forall (n_pre: Z) (PreH1 : (n_pre < 1)) (PreH2 : (problem_83_pre_z n_pre )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 9)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ False ”
.

Definition starts_one_ends_safety_wit_3 := 
forall (n_pre: Z) (PreH1 : (n_pre >= 1)) (PreH2 : (problem_83_pre_z n_pre )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 9)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition starts_one_ends_safety_wit_4 := 
forall (n_pre: Z) (PreH1 : (n_pre = 1)) (PreH2 : (n_pre >= 1)) (PreH3 : (problem_83_pre_z n_pre )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 9)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition starts_one_ends_safety_wit_5 := 
forall (n_pre: Z) (PreH1 : (n_pre <> 1)) (PreH2 : (n_pre >= 1)) (PreH3 : (problem_83_pre_z n_pre )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 9)) ,
  ((( &( "out" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (18 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 18) ”
.

Definition starts_one_ends_safety_wit_6 := 
forall (n_pre: Z) (PreH1 : (n_pre <> 1)) (PreH2 : (n_pre >= 1)) (PreH3 : (problem_83_pre_z n_pre )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 9)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "out" ) )) # Int  |-> 18)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition starts_one_ends_safety_wit_7 := 
forall (n_pre: Z) (out: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (out = (18 * (10^(i - 2 )) ))) (PreH5 : (n_pre <> 1)) (PreH6 : (n_pre >= 1)) (PreH7 : (problem_83_pre_z n_pre )) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 9)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> (out * 10 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition starts_one_ends_safety_wit_8 := 
(
forall (n_pre: Z) (out: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (out = (18 * (10^(i - 2 )) ))) (PreH5 : (n_pre <> 1)) (PreH6 : (n_pre >= 1)) (PreH7 : (problem_83_pre_z n_pre )) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 9)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((out * 10 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out * 10 )) ”
) \/
(
forall (n_pre: Z) (out: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (out = (18 * (10^(i - 2 )) ))) (PreH5 : (n_pre <> 1)) (PreH6 : (n_pre >= 1)) (PreH7 : (problem_83_pre_z n_pre )) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 9)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((out * 10 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out * 10 )) ”
).

Definition starts_one_ends_safety_wit_8_split_goal_1 := 
forall (n_pre: Z) (out: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (out = (18 * (10^(i - 2 )) ))) (PreH5 : (n_pre <> 1)) (PreH6 : (n_pre >= 1)) (PreH7 : (problem_83_pre_z n_pre )) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 9)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((out * 10 ) <= INT_MAX) ”
.

Definition starts_one_ends_safety_wit_8_split_goal_2 := 
forall (n_pre: Z) (out: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (out = (18 * (10^(i - 2 )) ))) (PreH5 : (n_pre <> 1)) (PreH6 : (n_pre >= 1)) (PreH7 : (problem_83_pre_z n_pre )) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 9)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((INT_MIN) <= (out * 10 )) ”
.

Definition starts_one_ends_safety_wit_9 := 
forall (n_pre: Z) (out: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (out = (18 * (10^(i - 2 )) ))) (PreH5 : (n_pre <> 1)) (PreH6 : (n_pre >= 1)) (PreH7 : (problem_83_pre_z n_pre )) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 9)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition starts_one_ends_entail_wit_1 := 
forall (n_pre: Z) (PreH1 : (n_pre <> 1)) (PreH2 : (n_pre >= 1)) (PreH3 : (problem_83_pre_z n_pre )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 9)) ,
  TT && emp 
|--
  “ (2 <= 2) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (18 = (18 * (10^(2 - 2 )) )) ” 
  &&  “ (n_pre <> 1) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (problem_83_pre_z n_pre ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 9) ”
  &&  emp
.

Definition starts_one_ends_entail_wit_2 := 
(
forall (n_pre: Z) (out: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (out = (18 * (10^(i - 2 )) ))) (PreH5 : (n_pre <> 1)) (PreH6 : (n_pre >= 1)) (PreH7 : (problem_83_pre_z n_pre )) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 9)) ,
  TT && emp 
|--
  “ (2 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((out * 10 ) = (18 * (10^((i + 1 ) - 2 )) )) ” 
  &&  “ (n_pre <> 1) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (problem_83_pre_z n_pre ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 9) ”
  &&  emp
) \/
(
forall (n_pre: Z) (out: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (out = (18 * (10^(i - 2 )) ))) (PreH5 : (n_pre <> 1)) (PreH6 : (n_pre >= 1)) (PreH7 : (problem_83_pre_z n_pre )) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 9)) ,
  TT && emp 
|--
  “ ((out * 10 ) = (18 * (10^((i + 1 ) - 2 )) )) ”
  &&  emp
).

Definition starts_one_ends_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (out: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (out = (18 * (10^(i - 2 )) ))) (PreH5 : (n_pre <> 1)) (PreH6 : (n_pre >= 1)) (PreH7 : (problem_83_pre_z n_pre )) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 9)) ,
  ((out * 10 ) = (18 * (10^((i + 1 ) - 2 )) ))
.

Definition starts_one_ends_return_wit_1 := 
(
forall (n_pre: Z) (out: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (out = (18 * (10^(i - 2 )) ))) (PreH5 : (n_pre <> 1)) (PreH6 : (n_pre >= 1)) (PreH7 : (problem_83_pre_z n_pre )) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 9)) ,
  TT && emp 
|--
  “ (problem_83_spec_z n_pre out ) ”
  &&  emp
) \/
(
forall (n_pre: Z) (out: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (out = (18 * (10^(i - 2 )) ))) (PreH5 : (n_pre <> 1)) (PreH6 : (n_pre >= 1)) (PreH7 : (problem_83_pre_z n_pre )) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 9)) ,
  TT && emp 
|--
  “ (problem_83_spec_z n_pre out ) ”
  &&  emp
).

Definition starts_one_ends_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (out: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (out = (18 * (10^(i - 2 )) ))) (PreH5 : (n_pre <> 1)) (PreH6 : (n_pre >= 1)) (PreH7 : (problem_83_pre_z n_pre )) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 9)) ,
  (problem_83_spec_z n_pre out )
.

Definition starts_one_ends_return_wit_2 := 
(
forall (n_pre: Z) (PreH1 : (n_pre = 1)) (PreH2 : (n_pre >= 1)) (PreH3 : (problem_83_pre_z n_pre )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 9)) ,
  TT && emp 
|--
  “ (problem_83_spec_z n_pre 1 ) ”
  &&  emp
) \/
(
forall (n_pre: Z) (PreH1 : (n_pre = 1)) (PreH2 : (n_pre >= 1)) (PreH3 : (problem_83_pre_z n_pre )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 9)) ,
  TT && emp 
|--
  “ (problem_83_spec_z n_pre 1 ) ”
  &&  emp
).

Definition starts_one_ends_return_wit_2_split_goal_1 := 
forall (n_pre: Z) (PreH1 : (n_pre = 1)) (PreH2 : (n_pre >= 1)) (PreH3 : (problem_83_pre_z n_pre )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 9)) ,
  (problem_83_spec_z n_pre 1 )
.

Module Type VC_Correct.


Axiom proof_of_starts_one_ends_safety_wit_1 : starts_one_ends_safety_wit_1.
Axiom proof_of_starts_one_ends_safety_wit_2 : starts_one_ends_safety_wit_2.
Axiom proof_of_starts_one_ends_safety_wit_3 : starts_one_ends_safety_wit_3.
Axiom proof_of_starts_one_ends_safety_wit_4 : starts_one_ends_safety_wit_4.
Axiom proof_of_starts_one_ends_safety_wit_5 : starts_one_ends_safety_wit_5.
Axiom proof_of_starts_one_ends_safety_wit_6 : starts_one_ends_safety_wit_6.
Axiom proof_of_starts_one_ends_safety_wit_7 : starts_one_ends_safety_wit_7.
Axiom proof_of_starts_one_ends_safety_wit_8 : starts_one_ends_safety_wit_8.
Axiom proof_of_starts_one_ends_safety_wit_9 : starts_one_ends_safety_wit_9.
Axiom proof_of_starts_one_ends_entail_wit_1 : starts_one_ends_entail_wit_1.
Axiom proof_of_starts_one_ends_entail_wit_2 : starts_one_ends_entail_wit_2.
Axiom proof_of_starts_one_ends_return_wit_1 : starts_one_ends_return_wit_1.
Axiom proof_of_starts_one_ends_return_wit_2 : starts_one_ends_return_wit_2.

End VC_Correct.
