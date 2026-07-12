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
Require Import p147_get_matrix_triples.
Local Open Scope sac.

(*----- Function get_matrix_triples -----*)

Definition get_matrix_triples_safety_wit_1 := 
forall (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1004)) (PreH3 : (problem_147_pre_z n_pre )) ,
  ((( &( "count" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_matrix_triples_safety_wit_2 := 
forall (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1004)) (PreH3 : (problem_147_pre_z n_pre )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_matrix_triples_safety_wit_3 := 
forall (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1004)) (PreH3 : (problem_147_pre_z n_pre )) ,
  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_matrix_triples_safety_wit_4 := 
forall (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1004)) (PreH3 : (problem_147_pre_z n_pre )) ,
  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_matrix_triples_safety_wit_5 := 
forall (n_pre: Z) (k_v: Z) (j_v: Z) (count: Z) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (count = (triples_i_147 (n_pre) (i)))) (PreH8 : (0 <= count)) (PreH9 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j_v)
  **  ((( &( "k" ) )) # Int  |-> k_v)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition get_matrix_triples_safety_wit_6 := 
forall (n_pre: Z) (k_v: Z) (j_v: Z) (count: Z) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (count = (triples_i_147 (n_pre) (i)))) (PreH8 : (0 <= count)) (PreH9 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j_v)
  **  ((( &( "k" ) )) # Int  |-> k_v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_matrix_triples_safety_wit_7 := 
forall (n_pre: Z) (k_v: Z) (count: Z) (j: Z) (i: Z) (PreH1 : (j <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= (n_pre + 1 ))) (PreH9 : (count = ((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ))) (PreH10 : (0 <= count)) (PreH11 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "k" ) )) # Int  |-> k_v)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition get_matrix_triples_safety_wit_8 := 
forall (n_pre: Z) (k_v: Z) (count: Z) (j: Z) (i: Z) (PreH1 : (j <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= (n_pre + 1 ))) (PreH9 : (count = ((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ))) (PreH10 : (0 <= count)) (PreH11 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "k" ) )) # Int  |-> k_v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_matrix_triples_safety_wit_9 := 
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (((((((i * i ) - i ) + 1 ) + (((j * j ) - j ) + 1 ) ) + (((k * k ) - k ) + 1 ) ) <> (INT_MIN)) \/ (3 <> (-1))) ” 
  &&  “ (3 <> 0) ”
.

Definition get_matrix_triples_safety_wit_10 := 
(
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((((((i * i ) - i ) + 1 ) + (((j * j ) - j ) + 1 ) ) + (((k * k ) - k ) + 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((((i * i ) - i ) + 1 ) + (((j * j ) - j ) + 1 ) ) + (((k * k ) - k ) + 1 ) )) ”
) \/
(
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((((((i * i ) - i ) + 1 ) + (((j * j ) - j ) + 1 ) ) + (((k * k ) - k ) + 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((((i * i ) - i ) + 1 ) + (((j * j ) - j ) + 1 ) ) + (((k * k ) - k ) + 1 ) )) ”
).

Definition get_matrix_triples_safety_wit_10_split_goal_1 := 
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((((((i * i ) - i ) + 1 ) + (((j * j ) - j ) + 1 ) ) + (((k * k ) - k ) + 1 ) ) <= INT_MAX) ”
.

Definition get_matrix_triples_safety_wit_10_split_goal_2 := 
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((INT_MIN) <= (((((i * i ) - i ) + 1 ) + (((j * j ) - j ) + 1 ) ) + (((k * k ) - k ) + 1 ) )) ”
.

Definition get_matrix_triples_safety_wit_11 := 
(
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((((k * k ) - k ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((k * k ) - k ) + 1 )) ”
) \/
(
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((((k * k ) - k ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((k * k ) - k ) + 1 )) ”
).

Definition get_matrix_triples_safety_wit_11_split_goal_1 := 
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((((k * k ) - k ) + 1 ) <= INT_MAX) ”
.

Definition get_matrix_triples_safety_wit_11_split_goal_2 := 
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((INT_MIN) <= (((k * k ) - k ) + 1 )) ”
.

Definition get_matrix_triples_safety_wit_12 := 
(
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (((k * k ) - k ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((k * k ) - k )) ”
) \/
(
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (((k * k ) - k ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((k * k ) - k )) ”
).

Definition get_matrix_triples_safety_wit_12_split_goal_1 := 
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (((k * k ) - k ) <= INT_MAX) ”
.

Definition get_matrix_triples_safety_wit_12_split_goal_2 := 
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((INT_MIN) <= ((k * k ) - k )) ”
.

Definition get_matrix_triples_safety_wit_13 := 
(
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((k * k ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k * k )) ”
) \/
(
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((k * k ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k * k )) ”
).

Definition get_matrix_triples_safety_wit_13_split_goal_1 := 
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((k * k ) <= INT_MAX) ”
.

Definition get_matrix_triples_safety_wit_13_split_goal_2 := 
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((INT_MIN) <= (k * k )) ”
.

Definition get_matrix_triples_safety_wit_14 := 
(
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (((((i * i ) - i ) + 1 ) + (((j * j ) - j ) + 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((i * i ) - i ) + 1 ) + (((j * j ) - j ) + 1 ) )) ”
) \/
(
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (((((i * i ) - i ) + 1 ) + (((j * j ) - j ) + 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((i * i ) - i ) + 1 ) + (((j * j ) - j ) + 1 ) )) ”
).

Definition get_matrix_triples_safety_wit_14_split_goal_1 := 
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (((((i * i ) - i ) + 1 ) + (((j * j ) - j ) + 1 ) ) <= INT_MAX) ”
.

Definition get_matrix_triples_safety_wit_14_split_goal_2 := 
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((INT_MIN) <= ((((i * i ) - i ) + 1 ) + (((j * j ) - j ) + 1 ) )) ”
.

Definition get_matrix_triples_safety_wit_15 := 
(
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((((j * j ) - j ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((j * j ) - j ) + 1 )) ”
) \/
(
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((((j * j ) - j ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((j * j ) - j ) + 1 )) ”
).

Definition get_matrix_triples_safety_wit_15_split_goal_1 := 
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((((j * j ) - j ) + 1 ) <= INT_MAX) ”
.

Definition get_matrix_triples_safety_wit_15_split_goal_2 := 
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((INT_MIN) <= (((j * j ) - j ) + 1 )) ”
.

Definition get_matrix_triples_safety_wit_16 := 
(
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (((j * j ) - j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((j * j ) - j )) ”
) \/
(
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (((j * j ) - j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((j * j ) - j )) ”
).

Definition get_matrix_triples_safety_wit_16_split_goal_1 := 
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (((j * j ) - j ) <= INT_MAX) ”
.

Definition get_matrix_triples_safety_wit_16_split_goal_2 := 
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((INT_MIN) <= ((j * j ) - j )) ”
.

Definition get_matrix_triples_safety_wit_17 := 
(
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((j * j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j * j )) ”
) \/
(
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((j * j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j * j )) ”
).

Definition get_matrix_triples_safety_wit_17_split_goal_1 := 
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((j * j ) <= INT_MAX) ”
.

Definition get_matrix_triples_safety_wit_17_split_goal_2 := 
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((INT_MIN) <= (j * j )) ”
.

Definition get_matrix_triples_safety_wit_18 := 
(
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((((i * i ) - i ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((i * i ) - i ) + 1 )) ”
) \/
(
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((((i * i ) - i ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((i * i ) - i ) + 1 )) ”
).

Definition get_matrix_triples_safety_wit_18_split_goal_1 := 
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((((i * i ) - i ) + 1 ) <= INT_MAX) ”
.

Definition get_matrix_triples_safety_wit_18_split_goal_2 := 
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((INT_MIN) <= (((i * i ) - i ) + 1 )) ”
.

Definition get_matrix_triples_safety_wit_19 := 
(
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (((i * i ) - i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i * i ) - i )) ”
) \/
(
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (((i * i ) - i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i * i ) - i )) ”
).

Definition get_matrix_triples_safety_wit_19_split_goal_1 := 
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (((i * i ) - i ) <= INT_MAX) ”
.

Definition get_matrix_triples_safety_wit_19_split_goal_2 := 
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((INT_MIN) <= ((i * i ) - i )) ”
.

Definition get_matrix_triples_safety_wit_20 := 
(
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((i * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * i )) ”
) \/
(
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((i * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * i )) ”
).

Definition get_matrix_triples_safety_wit_20_split_goal_1 := 
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((i * i ) <= INT_MAX) ”
.

Definition get_matrix_triples_safety_wit_20_split_goal_2 := 
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((INT_MIN) <= (i * i )) ”
.

Definition get_matrix_triples_safety_wit_21 := 
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_matrix_triples_safety_wit_22 := 
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_matrix_triples_safety_wit_23 := 
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_matrix_triples_safety_wit_24 := 
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition get_matrix_triples_safety_wit_25 := 
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_matrix_triples_safety_wit_26 := 
(
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (((((((i * i ) - i ) + 1 ) + (((j * j ) - j ) + 1 ) ) + (((k * k ) - k ) + 1 ) ) % ( 3 ) ) = 0)) (PreH2 : (k <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1004)) (PreH5 : (problem_147_pre_z n_pre )) (PreH6 : (1 <= i)) (PreH7 : (i < j)) (PreH8 : (j <= n_pre)) (PreH9 : ((j + 1 ) <= k)) (PreH10 : (k <= (n_pre + 1 ))) (PreH11 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH12 : (0 <= count)) (PreH13 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
) \/
(
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (((((((i * i ) - i ) + 1 ) + (((j * j ) - j ) + 1 ) ) + (((k * k ) - k ) + 1 ) ) % ( 3 ) ) = 0)) (PreH2 : (k <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1004)) (PreH5 : (problem_147_pre_z n_pre )) (PreH6 : (1 <= i)) (PreH7 : (i < j)) (PreH8 : (j <= n_pre)) (PreH9 : ((j + 1 ) <= k)) (PreH10 : (k <= (n_pre + 1 ))) (PreH11 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH12 : (0 <= count)) (PreH13 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
).

Definition get_matrix_triples_safety_wit_26_split_goal_1 := 
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (((((((i * i ) - i ) + 1 ) + (((j * j ) - j ) + 1 ) ) + (((k * k ) - k ) + 1 ) ) % ( 3 ) ) = 0)) (PreH2 : (k <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1004)) (PreH5 : (problem_147_pre_z n_pre )) (PreH6 : (1 <= i)) (PreH7 : (i < j)) (PreH8 : (j <= n_pre)) (PreH9 : ((j + 1 ) <= k)) (PreH10 : (k <= (n_pre + 1 ))) (PreH11 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH12 : (0 <= count)) (PreH13 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((count + 1 ) <= INT_MAX) ”
.

Definition get_matrix_triples_safety_wit_26_split_goal_2 := 
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (((((((i * i ) - i ) + 1 ) + (((j * j ) - j ) + 1 ) ) + (((k * k ) - k ) + 1 ) ) % ( 3 ) ) = 0)) (PreH2 : (k <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1004)) (PreH5 : (problem_147_pre_z n_pre )) (PreH6 : (1 <= i)) (PreH7 : (i < j)) (PreH8 : (j <= n_pre)) (PreH9 : ((j + 1 ) <= k)) (PreH10 : (k <= (n_pre + 1 ))) (PreH11 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH12 : (0 <= count)) (PreH13 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition get_matrix_triples_safety_wit_27 := 
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (((((((i * i ) - i ) + 1 ) + (((j * j ) - j ) + 1 ) ) + (((k * k ) - k ) + 1 ) ) % ( 3 ) ) = 0)) (PreH2 : (k <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1004)) (PreH5 : (problem_147_pre_z n_pre )) (PreH6 : (1 <= i)) (PreH7 : (i < j)) (PreH8 : (j <= n_pre)) (PreH9 : ((j + 1 ) <= k)) (PreH10 : (k <= (n_pre + 1 ))) (PreH11 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH12 : (0 <= count)) (PreH13 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition get_matrix_triples_safety_wit_28 := 
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (((((((i * i ) - i ) + 1 ) + (((j * j ) - j ) + 1 ) ) + (((k * k ) - k ) + 1 ) ) % ( 3 ) ) <> 0)) (PreH2 : (k <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1004)) (PreH5 : (problem_147_pre_z n_pre )) (PreH6 : (1 <= i)) (PreH7 : (i < j)) (PreH8 : (j <= n_pre)) (PreH9 : ((j + 1 ) <= k)) (PreH10 : (k <= (n_pre + 1 ))) (PreH11 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH12 : (0 <= count)) (PreH13 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition get_matrix_triples_safety_wit_29 := 
forall (n_pre: Z) (i: Z) (j: Z) (k: Z) (count: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1004)) (PreH3 : (problem_147_pre_z n_pre )) (PreH4 : (1 <= i)) (PreH5 : (i < j)) (PreH6 : (j <= n_pre)) (PreH7 : (k = (n_pre + 1 ))) (PreH8 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) ((n_pre + 1 ))) ))) (PreH9 : (0 <= count)) (PreH10 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition get_matrix_triples_safety_wit_30 := 
forall (n_pre: Z) (k_v: Z) (i: Z) (j: Z) (count: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1004)) (PreH3 : (problem_147_pre_z n_pre )) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (j = (n_pre + 1 ))) (PreH7 : (count = ((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) ((n_pre + 1 ))) ))) (PreH8 : (0 <= count)) (PreH9 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "k" ) )) # Int  |-> k_v)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition get_matrix_triples_entail_wit_1 := 
(
forall (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1004)) (PreH3 : (problem_147_pre_z n_pre )) ,
  TT && emp 
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1004) ” 
  &&  “ (problem_147_pre_z n_pre ) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (n_pre + 1 )) ” 
  &&  “ (0 = (triples_i_147 (n_pre) (1))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= INT_MAX) ”
  &&  emp
) \/
(
forall (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1004)) (PreH3 : (problem_147_pre_z n_pre )) ,
  TT && emp 
|--
  “ (0 = (triples_i_147 (n_pre) (1))) ”
  &&  emp
).

Definition get_matrix_triples_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1004)) (PreH3 : (problem_147_pre_z n_pre )) ,
  TT && emp 
|--
  “ (0 = (triples_i_147 (n_pre) (1))) ”
.

Definition get_matrix_triples_entail_wit_2 := 
(
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (count = (triples_i_147 (n_pre) (i)))) (PreH8 : (0 <= count)) (PreH9 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1004) ” 
  &&  “ (problem_147_pre_z n_pre ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((i + 1 ) <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (count = ((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) ((i + 1 ))) )) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= INT_MAX) ”
  &&  emp
) \/
(
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (count = (triples_i_147 (n_pre) (i)))) (PreH8 : (0 <= count)) (PreH9 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (count = ((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) ((i + 1 ))) )) ”
  &&  emp
).

Definition get_matrix_triples_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (count = (triples_i_147 (n_pre) (i)))) (PreH8 : (0 <= count)) (PreH9 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (count = ((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) ((i + 1 ))) )) ”
.

Definition get_matrix_triples_entail_wit_3 := 
(
forall (n_pre: Z) (count: Z) (j: Z) (i: Z) (PreH1 : (j <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= (n_pre + 1 ))) (PreH9 : (count = ((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ))) (PreH10 : (0 <= count)) (PreH11 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1004) ” 
  &&  “ (problem_147_pre_z n_pre ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ ((j + 1 ) <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) ((j + 1 ))) )) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= INT_MAX) ”
  &&  emp
) \/
(
forall (n_pre: Z) (count: Z) (j: Z) (i: Z) (PreH1 : (j <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= (n_pre + 1 ))) (PreH9 : (count = ((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ))) (PreH10 : (0 <= count)) (PreH11 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) ((j + 1 ))) )) ”
  &&  emp
).

Definition get_matrix_triples_entail_wit_3_split_goal_1 := 
forall (n_pre: Z) (count: Z) (j: Z) (i: Z) (PreH1 : (j <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= (n_pre + 1 ))) (PreH9 : (count = ((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ))) (PreH10 : (0 <= count)) (PreH11 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) ((j + 1 ))) )) ”
.

Definition get_matrix_triples_entail_wit_4_1 := 
(
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (((((((i * i ) - i ) + 1 ) + (((j * j ) - j ) + 1 ) ) + (((k * k ) - k ) + 1 ) ) % ( 3 ) ) = 0)) (PreH2 : (k <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1004)) (PreH5 : (problem_147_pre_z n_pre )) (PreH6 : (1 <= i)) (PreH7 : (i < j)) (PreH8 : (j <= n_pre)) (PreH9 : ((j + 1 ) <= k)) (PreH10 : (k <= (n_pre + 1 ))) (PreH11 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH12 : (0 <= count)) (PreH13 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1004) ” 
  &&  “ (problem_147_pre_z n_pre ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ ((j + 1 ) <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= (n_pre + 1 )) ” 
  &&  “ ((count + 1 ) = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) ((k + 1 ))) )) ” 
  &&  “ (0 <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= INT_MAX) ”
  &&  emp
) \/
(
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (((((((i * i ) - i ) + 1 ) + (((j * j ) - j ) + 1 ) ) + (((k * k ) - k ) + 1 ) ) % ( 3 ) ) = 0)) (PreH2 : (k <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1004)) (PreH5 : (problem_147_pre_z n_pre )) (PreH6 : (1 <= i)) (PreH7 : (i < j)) (PreH8 : (j <= n_pre)) (PreH9 : ((j + 1 ) <= k)) (PreH10 : (k <= (n_pre + 1 ))) (PreH11 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH12 : (0 <= count)) (PreH13 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((count + 1 ) = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) ((k + 1 ))) )) ”
  &&  emp
).

Definition get_matrix_triples_entail_wit_4_1_split_goal_1 := 
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (((((((i * i ) - i ) + 1 ) + (((j * j ) - j ) + 1 ) ) + (((k * k ) - k ) + 1 ) ) % ( 3 ) ) = 0)) (PreH2 : (k <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1004)) (PreH5 : (problem_147_pre_z n_pre )) (PreH6 : (1 <= i)) (PreH7 : (i < j)) (PreH8 : (j <= n_pre)) (PreH9 : ((j + 1 ) <= k)) (PreH10 : (k <= (n_pre + 1 ))) (PreH11 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH12 : (0 <= count)) (PreH13 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ ((count + 1 ) <= INT_MAX) ”
.

Definition get_matrix_triples_entail_wit_4_1_split_goal_2 := 
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (((((((i * i ) - i ) + 1 ) + (((j * j ) - j ) + 1 ) ) + (((k * k ) - k ) + 1 ) ) % ( 3 ) ) = 0)) (PreH2 : (k <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1004)) (PreH5 : (problem_147_pre_z n_pre )) (PreH6 : (1 <= i)) (PreH7 : (i < j)) (PreH8 : (j <= n_pre)) (PreH9 : ((j + 1 ) <= k)) (PreH10 : (k <= (n_pre + 1 ))) (PreH11 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH12 : (0 <= count)) (PreH13 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ ((count + 1 ) = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) ((k + 1 ))) )) ”
.

Definition get_matrix_triples_entail_wit_4_2 := 
(
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (((((((i * i ) - i ) + 1 ) + (((j * j ) - j ) + 1 ) ) + (((k * k ) - k ) + 1 ) ) % ( 3 ) ) <> 0)) (PreH2 : (k <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1004)) (PreH5 : (problem_147_pre_z n_pre )) (PreH6 : (1 <= i)) (PreH7 : (i < j)) (PreH8 : (j <= n_pre)) (PreH9 : ((j + 1 ) <= k)) (PreH10 : (k <= (n_pre + 1 ))) (PreH11 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH12 : (0 <= count)) (PreH13 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1004) ” 
  &&  “ (problem_147_pre_z n_pre ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ ((j + 1 ) <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) ((k + 1 ))) )) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= INT_MAX) ”
  &&  emp
) \/
(
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (((((((i * i ) - i ) + 1 ) + (((j * j ) - j ) + 1 ) ) + (((k * k ) - k ) + 1 ) ) % ( 3 ) ) <> 0)) (PreH2 : (k <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1004)) (PreH5 : (problem_147_pre_z n_pre )) (PreH6 : (1 <= i)) (PreH7 : (i < j)) (PreH8 : (j <= n_pre)) (PreH9 : ((j + 1 ) <= k)) (PreH10 : (k <= (n_pre + 1 ))) (PreH11 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH12 : (0 <= count)) (PreH13 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) ((k + 1 ))) )) ”
  &&  emp
).

Definition get_matrix_triples_entail_wit_4_2_split_goal_1 := 
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (((((((i * i ) - i ) + 1 ) + (((j * j ) - j ) + 1 ) ) + (((k * k ) - k ) + 1 ) ) % ( 3 ) ) <> 0)) (PreH2 : (k <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1004)) (PreH5 : (problem_147_pre_z n_pre )) (PreH6 : (1 <= i)) (PreH7 : (i < j)) (PreH8 : (j <= n_pre)) (PreH9 : ((j + 1 ) <= k)) (PreH10 : (k <= (n_pre + 1 ))) (PreH11 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH12 : (0 <= count)) (PreH13 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) ((k + 1 ))) )) ”
.

Definition get_matrix_triples_entail_wit_5 := 
(
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1004) ” 
  &&  “ (problem_147_pre_z n_pre ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (k = (n_pre + 1 )) ” 
  &&  “ (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) ((n_pre + 1 ))) )) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= INT_MAX) ”
  &&  emp
) \/
(
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) ((n_pre + 1 ))) )) ”
  &&  emp
).

Definition get_matrix_triples_entail_wit_5_split_goal_1 := 
forall (n_pre: Z) (count: Z) (k: Z) (j: Z) (i: Z) (PreH1 : (k > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i < j)) (PreH7 : (j <= n_pre)) (PreH8 : ((j + 1 ) <= k)) (PreH9 : (k <= (n_pre + 1 ))) (PreH10 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) (k)) ))) (PreH11 : (0 <= count)) (PreH12 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) ((n_pre + 1 ))) )) ”
.

Definition get_matrix_triples_entail_wit_6 := 
(
forall (n_pre: Z) (i: Z) (j: Z) (k: Z) (count: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1004)) (PreH3 : (problem_147_pre_z n_pre )) (PreH4 : (1 <= i)) (PreH5 : (i < j)) (PreH6 : (j <= n_pre)) (PreH7 : (k = (n_pre + 1 ))) (PreH8 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) ((n_pre + 1 ))) ))) (PreH9 : (0 <= count)) (PreH10 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1004) ” 
  &&  “ (problem_147_pre_z n_pre ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((i + 1 ) <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (count = ((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) ((j + 1 ))) )) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= INT_MAX) ”
  &&  emp
) \/
(
forall (n_pre: Z) (i: Z) (j: Z) (k: Z) (count: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1004)) (PreH3 : (problem_147_pre_z n_pre )) (PreH4 : (1 <= i)) (PreH5 : (i < j)) (PreH6 : (j <= n_pre)) (PreH7 : (k = (n_pre + 1 ))) (PreH8 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) ((n_pre + 1 ))) ))) (PreH9 : (0 <= count)) (PreH10 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (count = ((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) ((j + 1 ))) )) ”
  &&  emp
).

Definition get_matrix_triples_entail_wit_6_split_goal_1 := 
forall (n_pre: Z) (i: Z) (j: Z) (k: Z) (count: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1004)) (PreH3 : (problem_147_pre_z n_pre )) (PreH4 : (1 <= i)) (PreH5 : (i < j)) (PreH6 : (j <= n_pre)) (PreH7 : (k = (n_pre + 1 ))) (PreH8 : (count = (((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ) + (triples_k_147 (n_pre) (i) (j) ((n_pre + 1 ))) ))) (PreH9 : (0 <= count)) (PreH10 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (count = ((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) ((j + 1 ))) )) ”
.

Definition get_matrix_triples_entail_wit_7 := 
(
forall (n_pre: Z) (count: Z) (j: Z) (i: Z) (PreH1 : (j > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= (n_pre + 1 ))) (PreH9 : (count = ((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ))) (PreH10 : (0 <= count)) (PreH11 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1004) ” 
  &&  “ (problem_147_pre_z n_pre ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = (n_pre + 1 )) ” 
  &&  “ (count = ((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) ((n_pre + 1 ))) )) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= INT_MAX) ”
  &&  emp
) \/
(
forall (n_pre: Z) (count: Z) (j: Z) (i: Z) (PreH1 : (j > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= (n_pre + 1 ))) (PreH9 : (count = ((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ))) (PreH10 : (0 <= count)) (PreH11 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (count = ((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) ((n_pre + 1 ))) )) ”
  &&  emp
).

Definition get_matrix_triples_entail_wit_7_split_goal_1 := 
forall (n_pre: Z) (count: Z) (j: Z) (i: Z) (PreH1 : (j > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= (n_pre + 1 ))) (PreH9 : (count = ((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) (j)) ))) (PreH10 : (0 <= count)) (PreH11 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (count = ((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) ((n_pre + 1 ))) )) ”
.

Definition get_matrix_triples_entail_wit_8 := 
(
forall (n_pre: Z) (i: Z) (j: Z) (count: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1004)) (PreH3 : (problem_147_pre_z n_pre )) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (j = (n_pre + 1 ))) (PreH7 : (count = ((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) ((n_pre + 1 ))) ))) (PreH8 : (0 <= count)) (PreH9 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1004) ” 
  &&  “ (problem_147_pre_z n_pre ) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (count = (triples_i_147 (n_pre) ((i + 1 )))) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= INT_MAX) ”
  &&  emp
) \/
(
forall (n_pre: Z) (i: Z) (j: Z) (count: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1004)) (PreH3 : (problem_147_pre_z n_pre )) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (j = (n_pre + 1 ))) (PreH7 : (count = ((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) ((n_pre + 1 ))) ))) (PreH8 : (0 <= count)) (PreH9 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (count = (triples_i_147 (n_pre) ((i + 1 )))) ”
  &&  emp
).

Definition get_matrix_triples_entail_wit_8_split_goal_1 := 
forall (n_pre: Z) (i: Z) (j: Z) (count: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1004)) (PreH3 : (problem_147_pre_z n_pre )) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (j = (n_pre + 1 ))) (PreH7 : (count = ((triples_i_147 (n_pre) (i)) + (triples_j_147 (n_pre) (i) ((n_pre + 1 ))) ))) (PreH8 : (0 <= count)) (PreH9 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (count = (triples_i_147 (n_pre) ((i + 1 )))) ”
.

Definition get_matrix_triples_entail_wit_9 := 
(
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (count = (triples_i_147 (n_pre) (i)))) (PreH8 : (0 <= count)) (PreH9 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1004) ” 
  &&  “ (problem_147_pre_z n_pre ) ” 
  &&  “ (i = (n_pre + 1 )) ” 
  &&  “ (count = (triples_i_147 (n_pre) ((n_pre + 1 )))) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= INT_MAX) ”
  &&  emp
) \/
(
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (count = (triples_i_147 (n_pre) (i)))) (PreH8 : (0 <= count)) (PreH9 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (count = (triples_i_147 (n_pre) ((n_pre + 1 )))) ”
  &&  emp
).

Definition get_matrix_triples_entail_wit_9_split_goal_1 := 
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1004)) (PreH4 : (problem_147_pre_z n_pre )) (PreH5 : (1 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (count = (triples_i_147 (n_pre) (i)))) (PreH8 : (0 <= count)) (PreH9 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (count = (triples_i_147 (n_pre) ((n_pre + 1 )))) ”
.

Definition get_matrix_triples_return_wit_1 := 
(
forall (n_pre: Z) (i: Z) (count: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1004)) (PreH3 : (problem_147_pre_z n_pre )) (PreH4 : (i = (n_pre + 1 ))) (PreH5 : (count = (triples_i_147 (n_pre) ((n_pre + 1 ))))) (PreH6 : (0 <= count)) (PreH7 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (problem_147_spec_z n_pre count ) ”
  &&  emp
) \/
(
forall (n_pre: Z) (i: Z) (count: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1004)) (PreH3 : (problem_147_pre_z n_pre )) (PreH4 : (i = (n_pre + 1 ))) (PreH5 : (count = (triples_i_147 (n_pre) ((n_pre + 1 ))))) (PreH6 : (0 <= count)) (PreH7 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (problem_147_spec_z n_pre count ) ”
  &&  emp
).

Definition get_matrix_triples_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (i: Z) (count: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1004)) (PreH3 : (problem_147_pre_z n_pre )) (PreH4 : (i = (n_pre + 1 ))) (PreH5 : (count = (triples_i_147 (n_pre) ((n_pre + 1 ))))) (PreH6 : (0 <= count)) (PreH7 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (problem_147_spec_z n_pre count ) ”
.

Module Type VC_Correct.


Axiom proof_of_get_matrix_triples_safety_wit_1 : get_matrix_triples_safety_wit_1.
Axiom proof_of_get_matrix_triples_safety_wit_2 : get_matrix_triples_safety_wit_2.
Axiom proof_of_get_matrix_triples_safety_wit_3 : get_matrix_triples_safety_wit_3.
Axiom proof_of_get_matrix_triples_safety_wit_4 : get_matrix_triples_safety_wit_4.
Axiom proof_of_get_matrix_triples_safety_wit_5 : get_matrix_triples_safety_wit_5.
Axiom proof_of_get_matrix_triples_safety_wit_6 : get_matrix_triples_safety_wit_6.
Axiom proof_of_get_matrix_triples_safety_wit_7 : get_matrix_triples_safety_wit_7.
Axiom proof_of_get_matrix_triples_safety_wit_8 : get_matrix_triples_safety_wit_8.
Axiom proof_of_get_matrix_triples_safety_wit_9 : get_matrix_triples_safety_wit_9.
Axiom proof_of_get_matrix_triples_safety_wit_10 : get_matrix_triples_safety_wit_10.
Axiom proof_of_get_matrix_triples_safety_wit_11 : get_matrix_triples_safety_wit_11.
Axiom proof_of_get_matrix_triples_safety_wit_12 : get_matrix_triples_safety_wit_12.
Axiom proof_of_get_matrix_triples_safety_wit_13 : get_matrix_triples_safety_wit_13.
Axiom proof_of_get_matrix_triples_safety_wit_14 : get_matrix_triples_safety_wit_14.
Axiom proof_of_get_matrix_triples_safety_wit_15 : get_matrix_triples_safety_wit_15.
Axiom proof_of_get_matrix_triples_safety_wit_16 : get_matrix_triples_safety_wit_16.
Axiom proof_of_get_matrix_triples_safety_wit_17 : get_matrix_triples_safety_wit_17.
Axiom proof_of_get_matrix_triples_safety_wit_18 : get_matrix_triples_safety_wit_18.
Axiom proof_of_get_matrix_triples_safety_wit_19 : get_matrix_triples_safety_wit_19.
Axiom proof_of_get_matrix_triples_safety_wit_20 : get_matrix_triples_safety_wit_20.
Axiom proof_of_get_matrix_triples_safety_wit_21 : get_matrix_triples_safety_wit_21.
Axiom proof_of_get_matrix_triples_safety_wit_22 : get_matrix_triples_safety_wit_22.
Axiom proof_of_get_matrix_triples_safety_wit_23 : get_matrix_triples_safety_wit_23.
Axiom proof_of_get_matrix_triples_safety_wit_24 : get_matrix_triples_safety_wit_24.
Axiom proof_of_get_matrix_triples_safety_wit_25 : get_matrix_triples_safety_wit_25.
Axiom proof_of_get_matrix_triples_safety_wit_26 : get_matrix_triples_safety_wit_26.
Axiom proof_of_get_matrix_triples_safety_wit_27 : get_matrix_triples_safety_wit_27.
Axiom proof_of_get_matrix_triples_safety_wit_28 : get_matrix_triples_safety_wit_28.
Axiom proof_of_get_matrix_triples_safety_wit_29 : get_matrix_triples_safety_wit_29.
Axiom proof_of_get_matrix_triples_safety_wit_30 : get_matrix_triples_safety_wit_30.
Axiom proof_of_get_matrix_triples_entail_wit_1 : get_matrix_triples_entail_wit_1.
Axiom proof_of_get_matrix_triples_entail_wit_2 : get_matrix_triples_entail_wit_2.
Axiom proof_of_get_matrix_triples_entail_wit_3 : get_matrix_triples_entail_wit_3.
Axiom proof_of_get_matrix_triples_entail_wit_4_1 : get_matrix_triples_entail_wit_4_1.
Axiom proof_of_get_matrix_triples_entail_wit_4_2 : get_matrix_triples_entail_wit_4_2.
Axiom proof_of_get_matrix_triples_entail_wit_5 : get_matrix_triples_entail_wit_5.
Axiom proof_of_get_matrix_triples_entail_wit_6 : get_matrix_triples_entail_wit_6.
Axiom proof_of_get_matrix_triples_entail_wit_7 : get_matrix_triples_entail_wit_7.
Axiom proof_of_get_matrix_triples_entail_wit_8 : get_matrix_triples_entail_wit_8.
Axiom proof_of_get_matrix_triples_entail_wit_9 : get_matrix_triples_entail_wit_9.
Axiom proof_of_get_matrix_triples_return_wit_1 : get_matrix_triples_return_wit_1.

End VC_Correct.
