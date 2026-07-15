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
Require Import p071_triangle_area.
Local Open Scope sac.

(*----- Function triangle_area -----*)

Definition triangle_area_safety_wit_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition triangle_area_safety_wit_2 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre > 0)) (PreH2 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition triangle_area_safety_wit_3 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (b_pre > 0)) (PreH2 : (a_pre > 0)) (PreH3 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition triangle_area_safety_wit_4 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (c_pre <= 0)) (PreH2 : (b_pre > 0)) (PreH3 : (a_pre > 0)) (PreH4 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition triangle_area_safety_wit_5 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <= 0)) (PreH2 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition triangle_area_safety_wit_6 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (b_pre <= 0)) (PreH2 : (a_pre > 0)) (PreH3 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition triangle_area_safety_wit_7 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (b_pre <= 0)) (PreH2 : (a_pre > 0)) (PreH3 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition triangle_area_safety_wit_8 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <= 0)) (PreH2 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition triangle_area_safety_wit_9 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (c_pre <= 0)) (PreH2 : (b_pre > 0)) (PreH3 : (a_pre > 0)) (PreH4 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition triangle_area_safety_wit_10 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (c_pre > 0)) (PreH2 : (b_pre > 0)) (PreH3 : (a_pre > 0)) (PreH4 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((a_pre + b_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (a_pre + b_pre )) ”
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (c_pre > 0)) (PreH2 : (b_pre > 0)) (PreH3 : (a_pre > 0)) (PreH4 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((a_pre + b_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (a_pre + b_pre )) ”
).

Definition triangle_area_safety_wit_10_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (c_pre > 0)) (PreH2 : (b_pre > 0)) (PreH3 : (a_pre > 0)) (PreH4 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((a_pre + b_pre ) <= INT_MAX) ”
.

Definition triangle_area_safety_wit_10_split_goal_2 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (c_pre > 0)) (PreH2 : (b_pre > 0)) (PreH3 : (a_pre > 0)) (PreH4 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((INT_MIN) <= (a_pre + b_pre )) ”
.

Definition triangle_area_safety_wit_11 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((a_pre + b_pre ) > c_pre)) (PreH2 : (c_pre > 0)) (PreH3 : (b_pre > 0)) (PreH4 : (a_pre > 0)) (PreH5 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((a_pre + c_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (a_pre + c_pre )) ”
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((a_pre + b_pre ) > c_pre)) (PreH2 : (c_pre > 0)) (PreH3 : (b_pre > 0)) (PreH4 : (a_pre > 0)) (PreH5 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((a_pre + c_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (a_pre + c_pre )) ”
).

Definition triangle_area_safety_wit_11_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((a_pre + b_pre ) > c_pre)) (PreH2 : (c_pre > 0)) (PreH3 : (b_pre > 0)) (PreH4 : (a_pre > 0)) (PreH5 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((a_pre + c_pre ) <= INT_MAX) ”
.

Definition triangle_area_safety_wit_11_split_goal_2 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((a_pre + b_pre ) > c_pre)) (PreH2 : (c_pre > 0)) (PreH3 : (b_pre > 0)) (PreH4 : (a_pre > 0)) (PreH5 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((INT_MIN) <= (a_pre + c_pre )) ”
.

Definition triangle_area_safety_wit_12 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((a_pre + c_pre ) > b_pre)) (PreH2 : ((a_pre + b_pre ) > c_pre)) (PreH3 : (c_pre > 0)) (PreH4 : (b_pre > 0)) (PreH5 : (a_pre > 0)) (PreH6 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((b_pre + c_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (b_pre + c_pre )) ”
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((a_pre + c_pre ) > b_pre)) (PreH2 : ((a_pre + b_pre ) > c_pre)) (PreH3 : (c_pre > 0)) (PreH4 : (b_pre > 0)) (PreH5 : (a_pre > 0)) (PreH6 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((b_pre + c_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (b_pre + c_pre )) ”
).

Definition triangle_area_safety_wit_12_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((a_pre + c_pre ) > b_pre)) (PreH2 : ((a_pre + b_pre ) > c_pre)) (PreH3 : (c_pre > 0)) (PreH4 : (b_pre > 0)) (PreH5 : (a_pre > 0)) (PreH6 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((b_pre + c_pre ) <= INT_MAX) ”
.

Definition triangle_area_safety_wit_12_split_goal_2 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((a_pre + c_pre ) > b_pre)) (PreH2 : ((a_pre + b_pre ) > c_pre)) (PreH3 : (c_pre > 0)) (PreH4 : (b_pre > 0)) (PreH5 : (a_pre > 0)) (PreH6 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((INT_MIN) <= (b_pre + c_pre )) ”
.

Definition triangle_area_safety_wit_13 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((b_pre + c_pre ) <= a_pre)) (PreH2 : ((a_pre + c_pre ) > b_pre)) (PreH3 : ((a_pre + b_pre ) > c_pre)) (PreH4 : (c_pre > 0)) (PreH5 : (b_pre > 0)) (PreH6 : (a_pre > 0)) (PreH7 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition triangle_area_safety_wit_14 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((a_pre + b_pre ) <= c_pre)) (PreH2 : (c_pre > 0)) (PreH3 : (b_pre > 0)) (PreH4 : (a_pre > 0)) (PreH5 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition triangle_area_safety_wit_15 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((a_pre + c_pre ) <= b_pre)) (PreH2 : ((a_pre + b_pre ) > c_pre)) (PreH3 : (c_pre > 0)) (PreH4 : (b_pre > 0)) (PreH5 : (a_pre > 0)) (PreH6 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition triangle_area_safety_wit_16 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((a_pre + c_pre ) <= b_pre)) (PreH2 : ((a_pre + b_pre ) > c_pre)) (PreH3 : (c_pre > 0)) (PreH4 : (b_pre > 0)) (PreH5 : (a_pre > 0)) (PreH6 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition triangle_area_safety_wit_17 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((a_pre + b_pre ) <= c_pre)) (PreH2 : (c_pre > 0)) (PreH3 : (b_pre > 0)) (PreH4 : (a_pre > 0)) (PreH5 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition triangle_area_safety_wit_18 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((b_pre + c_pre ) <= a_pre)) (PreH2 : ((a_pre + c_pre ) > b_pre)) (PreH3 : ((a_pre + b_pre ) > c_pre)) (PreH4 : (c_pre > 0)) (PreH5 : (b_pre > 0)) (PreH6 : (a_pre > 0)) (PreH7 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition triangle_area_safety_wit_19 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((b_pre + c_pre ) > a_pre)) (PreH2 : ((a_pre + c_pre ) > b_pre)) (PreH3 : ((a_pre + b_pre ) > c_pre)) (PreH4 : (c_pre > 0)) (PreH5 : (b_pre > 0)) (PreH6 : (a_pre > 0)) (PreH7 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (((a_pre + b_pre ) + c_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((a_pre + b_pre ) + c_pre )) ”
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((b_pre + c_pre ) > a_pre)) (PreH2 : ((a_pre + c_pre ) > b_pre)) (PreH3 : ((a_pre + b_pre ) > c_pre)) (PreH4 : (c_pre > 0)) (PreH5 : (b_pre > 0)) (PreH6 : (a_pre > 0)) (PreH7 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (((a_pre + b_pre ) + c_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((a_pre + b_pre ) + c_pre )) ”
).

Definition triangle_area_safety_wit_19_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((b_pre + c_pre ) > a_pre)) (PreH2 : ((a_pre + c_pre ) > b_pre)) (PreH3 : ((a_pre + b_pre ) > c_pre)) (PreH4 : (c_pre > 0)) (PreH5 : (b_pre > 0)) (PreH6 : (a_pre > 0)) (PreH7 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (((a_pre + b_pre ) + c_pre ) <= INT_MAX) ”
.

Definition triangle_area_safety_wit_19_split_goal_2 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((b_pre + c_pre ) > a_pre)) (PreH2 : ((a_pre + c_pre ) > b_pre)) (PreH3 : ((a_pre + b_pre ) > c_pre)) (PreH4 : (c_pre > 0)) (PreH5 : (b_pre > 0)) (PreH6 : (a_pre > 0)) (PreH7 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((INT_MIN) <= ((a_pre + b_pre ) + c_pre )) ”
.

Definition triangle_area_safety_wit_20 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((b_pre + c_pre ) > a_pre)) (PreH2 : ((a_pre + c_pre ) > b_pre)) (PreH3 : ((a_pre + b_pre ) > c_pre)) (PreH4 : (c_pre > 0)) (PreH5 : (b_pre > 0)) (PreH6 : (a_pre > 0)) (PreH7 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((a_pre + b_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (a_pre + b_pre )) ”
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((b_pre + c_pre ) > a_pre)) (PreH2 : ((a_pre + c_pre ) > b_pre)) (PreH3 : ((a_pre + b_pre ) > c_pre)) (PreH4 : (c_pre > 0)) (PreH5 : (b_pre > 0)) (PreH6 : (a_pre > 0)) (PreH7 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((a_pre + b_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (a_pre + b_pre )) ”
).

Definition triangle_area_safety_wit_20_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((b_pre + c_pre ) > a_pre)) (PreH2 : ((a_pre + c_pre ) > b_pre)) (PreH3 : ((a_pre + b_pre ) > c_pre)) (PreH4 : (c_pre > 0)) (PreH5 : (b_pre > 0)) (PreH6 : (a_pre > 0)) (PreH7 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((a_pre + b_pre ) <= INT_MAX) ”
.

Definition triangle_area_safety_wit_20_split_goal_2 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((b_pre + c_pre ) > a_pre)) (PreH2 : ((a_pre + c_pre ) > b_pre)) (PreH3 : ((a_pre + b_pre ) > c_pre)) (PreH4 : (c_pre > 0)) (PreH5 : (b_pre > 0)) (PreH6 : (a_pre > 0)) (PreH7 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((INT_MIN) <= (a_pre + b_pre )) ”
.

Definition triangle_area_safety_wit_21 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((b_pre + c_pre ) > a_pre)) (PreH2 : ((a_pre + c_pre ) > b_pre)) (PreH3 : ((a_pre + b_pre ) > c_pre)) (PreH4 : (c_pre > 0)) (PreH5 : (b_pre > 0)) (PreH6 : (a_pre > 0)) (PreH7 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "y" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |-> ((a_pre + b_pre ) + c_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((((-a_pre) + b_pre ) + c_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((-a_pre) + b_pre ) + c_pre )) ”
.

Definition triangle_area_safety_wit_22 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((b_pre + c_pre ) > a_pre)) (PreH2 : ((a_pre + c_pre ) > b_pre)) (PreH3 : ((a_pre + b_pre ) > c_pre)) (PreH4 : (c_pre > 0)) (PreH5 : (b_pre > 0)) (PreH6 : (a_pre > 0)) (PreH7 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "y" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |-> ((a_pre + b_pre ) + c_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (((-a_pre) + b_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((-a_pre) + b_pre )) ”
.

Definition triangle_area_safety_wit_23 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((b_pre + c_pre ) > a_pre)) (PreH2 : ((a_pre + c_pre ) > b_pre)) (PreH3 : ((a_pre + b_pre ) > c_pre)) (PreH4 : (c_pre > 0)) (PreH5 : (b_pre > 0)) (PreH6 : (a_pre > 0)) (PreH7 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "y" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |-> ((a_pre + b_pre ) + c_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (a_pre <> (INT_MIN)) ”
.

Definition triangle_area_safety_wit_24 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((b_pre + c_pre ) > a_pre)) (PreH2 : ((a_pre + c_pre ) > b_pre)) (PreH3 : ((a_pre + b_pre ) > c_pre)) (PreH4 : (c_pre > 0)) (PreH5 : (b_pre > 0)) (PreH6 : (a_pre > 0)) (PreH7 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "z" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> (((-a_pre) + b_pre ) + c_pre ))
  **  ((( &( "x" ) )) # Int  |-> ((a_pre + b_pre ) + c_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (((a_pre - b_pre ) + c_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((a_pre - b_pre ) + c_pre )) ”
.

Definition triangle_area_safety_wit_25 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((b_pre + c_pre ) > a_pre)) (PreH2 : ((a_pre + c_pre ) > b_pre)) (PreH3 : ((a_pre + b_pre ) > c_pre)) (PreH4 : (c_pre > 0)) (PreH5 : (b_pre > 0)) (PreH6 : (a_pre > 0)) (PreH7 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "z" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> (((-a_pre) + b_pre ) + c_pre ))
  **  ((( &( "x" ) )) # Int  |-> ((a_pre + b_pre ) + c_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((a_pre - b_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (a_pre - b_pre )) ”
.

Definition triangle_area_safety_wit_26 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((b_pre + c_pre ) > a_pre)) (PreH2 : ((a_pre + c_pre ) > b_pre)) (PreH3 : ((a_pre + b_pre ) > c_pre)) (PreH4 : (c_pre > 0)) (PreH5 : (b_pre > 0)) (PreH6 : (a_pre > 0)) (PreH7 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "z" ) )) # Int  |-> ((a_pre - b_pre ) + c_pre ))
  **  ((( &( "y" ) )) # Int  |-> (((-a_pre) + b_pre ) + c_pre ))
  **  ((( &( "x" ) )) # Int  |-> ((a_pre + b_pre ) + c_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (((a_pre + b_pre ) - c_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((a_pre + b_pre ) - c_pre )) ”
.

Definition triangle_area_safety_wit_27 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((b_pre + c_pre ) > a_pre)) (PreH2 : ((a_pre + c_pre ) > b_pre)) (PreH3 : ((a_pre + b_pre ) > c_pre)) (PreH4 : (c_pre > 0)) (PreH5 : (b_pre > 0)) (PreH6 : (a_pre > 0)) (PreH7 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "z" ) )) # Int  |-> ((a_pre - b_pre ) + c_pre ))
  **  ((( &( "y" ) )) # Int  |-> (((-a_pre) + b_pre ) + c_pre ))
  **  ((( &( "x" ) )) # Int  |-> ((a_pre + b_pre ) + c_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((a_pre + b_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (a_pre + b_pre )) ”
.

Definition triangle_area_safety_wit_28 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((b_pre + c_pre ) > a_pre)) (PreH2 : ((a_pre + c_pre ) > b_pre)) (PreH3 : ((a_pre + b_pre ) > c_pre)) (PreH4 : (c_pre > 0)) (PreH5 : (b_pre > 0)) (PreH6 : (a_pre > 0)) (PreH7 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "w" ) )) # Int  |-> ((a_pre + b_pre ) - c_pre ))
  **  ((( &( "z" ) )) # Int  |-> ((a_pre - b_pre ) + c_pre ))
  **  ((( &( "y" ) )) # Int  |-> (((-a_pre) + b_pre ) + c_pre ))
  **  ((( &( "x" ) )) # Int  |-> ((a_pre + b_pre ) + c_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((((((a_pre + b_pre ) + c_pre ) * (((-a_pre) + b_pre ) + c_pre ) ) * ((a_pre - b_pre ) + c_pre ) ) * ((a_pre + b_pre ) - c_pre ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((((a_pre + b_pre ) + c_pre ) * (((-a_pre) + b_pre ) + c_pre ) ) * ((a_pre - b_pre ) + c_pre ) ) * ((a_pre + b_pre ) - c_pre ) )) ”
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((b_pre + c_pre ) > a_pre)) (PreH2 : ((a_pre + c_pre ) > b_pre)) (PreH3 : ((a_pre + b_pre ) > c_pre)) (PreH4 : (c_pre > 0)) (PreH5 : (b_pre > 0)) (PreH6 : (a_pre > 0)) (PreH7 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "w" ) )) # Int  |-> ((a_pre + b_pre ) - c_pre ))
  **  ((( &( "z" ) )) # Int  |-> ((a_pre - b_pre ) + c_pre ))
  **  ((( &( "y" ) )) # Int  |-> (((-a_pre) + b_pre ) + c_pre ))
  **  ((( &( "x" ) )) # Int  |-> ((a_pre + b_pre ) + c_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((((((a_pre + b_pre ) + c_pre ) * (((-a_pre) + b_pre ) + c_pre ) ) * ((a_pre - b_pre ) + c_pre ) ) * ((a_pre + b_pre ) - c_pre ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((((a_pre + b_pre ) + c_pre ) * (((-a_pre) + b_pre ) + c_pre ) ) * ((a_pre - b_pre ) + c_pre ) ) * ((a_pre + b_pre ) - c_pre ) )) ”
).

Definition triangle_area_safety_wit_28_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((b_pre + c_pre ) > a_pre)) (PreH2 : ((a_pre + c_pre ) > b_pre)) (PreH3 : ((a_pre + b_pre ) > c_pre)) (PreH4 : (c_pre > 0)) (PreH5 : (b_pre > 0)) (PreH6 : (a_pre > 0)) (PreH7 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "w" ) )) # Int  |-> ((a_pre + b_pre ) - c_pre ))
  **  ((( &( "z" ) )) # Int  |-> ((a_pre - b_pre ) + c_pre ))
  **  ((( &( "y" ) )) # Int  |-> (((-a_pre) + b_pre ) + c_pre ))
  **  ((( &( "x" ) )) # Int  |-> ((a_pre + b_pre ) + c_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((((((a_pre + b_pre ) + c_pre ) * (((-a_pre) + b_pre ) + c_pre ) ) * ((a_pre - b_pre ) + c_pre ) ) * ((a_pre + b_pre ) - c_pre ) ) <= INT_MAX) ”
.

Definition triangle_area_safety_wit_28_split_goal_2 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((b_pre + c_pre ) > a_pre)) (PreH2 : ((a_pre + c_pre ) > b_pre)) (PreH3 : ((a_pre + b_pre ) > c_pre)) (PreH4 : (c_pre > 0)) (PreH5 : (b_pre > 0)) (PreH6 : (a_pre > 0)) (PreH7 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "w" ) )) # Int  |-> ((a_pre + b_pre ) - c_pre ))
  **  ((( &( "z" ) )) # Int  |-> ((a_pre - b_pre ) + c_pre ))
  **  ((( &( "y" ) )) # Int  |-> (((-a_pre) + b_pre ) + c_pre ))
  **  ((( &( "x" ) )) # Int  |-> ((a_pre + b_pre ) + c_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((INT_MIN) <= (((((a_pre + b_pre ) + c_pre ) * (((-a_pre) + b_pre ) + c_pre ) ) * ((a_pre - b_pre ) + c_pre ) ) * ((a_pre + b_pre ) - c_pre ) )) ”
.

Definition triangle_area_safety_wit_29 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((b_pre + c_pre ) > a_pre)) (PreH2 : ((a_pre + c_pre ) > b_pre)) (PreH3 : ((a_pre + b_pre ) > c_pre)) (PreH4 : (c_pre > 0)) (PreH5 : (b_pre > 0)) (PreH6 : (a_pre > 0)) (PreH7 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "w" ) )) # Int  |-> ((a_pre + b_pre ) - c_pre ))
  **  ((( &( "z" ) )) # Int  |-> ((a_pre - b_pre ) + c_pre ))
  **  ((( &( "y" ) )) # Int  |-> (((-a_pre) + b_pre ) + c_pre ))
  **  ((( &( "x" ) )) # Int  |-> ((a_pre + b_pre ) + c_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (((((a_pre + b_pre ) + c_pre ) * (((-a_pre) + b_pre ) + c_pre ) ) * ((a_pre - b_pre ) + c_pre ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((a_pre + b_pre ) + c_pre ) * (((-a_pre) + b_pre ) + c_pre ) ) * ((a_pre - b_pre ) + c_pre ) )) ”
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((b_pre + c_pre ) > a_pre)) (PreH2 : ((a_pre + c_pre ) > b_pre)) (PreH3 : ((a_pre + b_pre ) > c_pre)) (PreH4 : (c_pre > 0)) (PreH5 : (b_pre > 0)) (PreH6 : (a_pre > 0)) (PreH7 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "w" ) )) # Int  |-> ((a_pre + b_pre ) - c_pre ))
  **  ((( &( "z" ) )) # Int  |-> ((a_pre - b_pre ) + c_pre ))
  **  ((( &( "y" ) )) # Int  |-> (((-a_pre) + b_pre ) + c_pre ))
  **  ((( &( "x" ) )) # Int  |-> ((a_pre + b_pre ) + c_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (((((a_pre + b_pre ) + c_pre ) * (((-a_pre) + b_pre ) + c_pre ) ) * ((a_pre - b_pre ) + c_pre ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((a_pre + b_pre ) + c_pre ) * (((-a_pre) + b_pre ) + c_pre ) ) * ((a_pre - b_pre ) + c_pre ) )) ”
).

Definition triangle_area_safety_wit_29_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((b_pre + c_pre ) > a_pre)) (PreH2 : ((a_pre + c_pre ) > b_pre)) (PreH3 : ((a_pre + b_pre ) > c_pre)) (PreH4 : (c_pre > 0)) (PreH5 : (b_pre > 0)) (PreH6 : (a_pre > 0)) (PreH7 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "w" ) )) # Int  |-> ((a_pre + b_pre ) - c_pre ))
  **  ((( &( "z" ) )) # Int  |-> ((a_pre - b_pre ) + c_pre ))
  **  ((( &( "y" ) )) # Int  |-> (((-a_pre) + b_pre ) + c_pre ))
  **  ((( &( "x" ) )) # Int  |-> ((a_pre + b_pre ) + c_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (((((a_pre + b_pre ) + c_pre ) * (((-a_pre) + b_pre ) + c_pre ) ) * ((a_pre - b_pre ) + c_pre ) ) <= INT_MAX) ”
.

Definition triangle_area_safety_wit_29_split_goal_2 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((b_pre + c_pre ) > a_pre)) (PreH2 : ((a_pre + c_pre ) > b_pre)) (PreH3 : ((a_pre + b_pre ) > c_pre)) (PreH4 : (c_pre > 0)) (PreH5 : (b_pre > 0)) (PreH6 : (a_pre > 0)) (PreH7 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "w" ) )) # Int  |-> ((a_pre + b_pre ) - c_pre ))
  **  ((( &( "z" ) )) # Int  |-> ((a_pre - b_pre ) + c_pre ))
  **  ((( &( "y" ) )) # Int  |-> (((-a_pre) + b_pre ) + c_pre ))
  **  ((( &( "x" ) )) # Int  |-> ((a_pre + b_pre ) + c_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((INT_MIN) <= ((((a_pre + b_pre ) + c_pre ) * (((-a_pre) + b_pre ) + c_pre ) ) * ((a_pre - b_pre ) + c_pre ) )) ”
.

Definition triangle_area_safety_wit_30 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((b_pre + c_pre ) > a_pre)) (PreH2 : ((a_pre + c_pre ) > b_pre)) (PreH3 : ((a_pre + b_pre ) > c_pre)) (PreH4 : (c_pre > 0)) (PreH5 : (b_pre > 0)) (PreH6 : (a_pre > 0)) (PreH7 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "w" ) )) # Int  |-> ((a_pre + b_pre ) - c_pre ))
  **  ((( &( "z" ) )) # Int  |-> ((a_pre - b_pre ) + c_pre ))
  **  ((( &( "y" ) )) # Int  |-> (((-a_pre) + b_pre ) + c_pre ))
  **  ((( &( "x" ) )) # Int  |-> ((a_pre + b_pre ) + c_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((((a_pre + b_pre ) + c_pre ) * (((-a_pre) + b_pre ) + c_pre ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((a_pre + b_pre ) + c_pre ) * (((-a_pre) + b_pre ) + c_pre ) )) ”
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((b_pre + c_pre ) > a_pre)) (PreH2 : ((a_pre + c_pre ) > b_pre)) (PreH3 : ((a_pre + b_pre ) > c_pre)) (PreH4 : (c_pre > 0)) (PreH5 : (b_pre > 0)) (PreH6 : (a_pre > 0)) (PreH7 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "w" ) )) # Int  |-> ((a_pre + b_pre ) - c_pre ))
  **  ((( &( "z" ) )) # Int  |-> ((a_pre - b_pre ) + c_pre ))
  **  ((( &( "y" ) )) # Int  |-> (((-a_pre) + b_pre ) + c_pre ))
  **  ((( &( "x" ) )) # Int  |-> ((a_pre + b_pre ) + c_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((((a_pre + b_pre ) + c_pre ) * (((-a_pre) + b_pre ) + c_pre ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((a_pre + b_pre ) + c_pre ) * (((-a_pre) + b_pre ) + c_pre ) )) ”
).

Definition triangle_area_safety_wit_30_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((b_pre + c_pre ) > a_pre)) (PreH2 : ((a_pre + c_pre ) > b_pre)) (PreH3 : ((a_pre + b_pre ) > c_pre)) (PreH4 : (c_pre > 0)) (PreH5 : (b_pre > 0)) (PreH6 : (a_pre > 0)) (PreH7 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "w" ) )) # Int  |-> ((a_pre + b_pre ) - c_pre ))
  **  ((( &( "z" ) )) # Int  |-> ((a_pre - b_pre ) + c_pre ))
  **  ((( &( "y" ) )) # Int  |-> (((-a_pre) + b_pre ) + c_pre ))
  **  ((( &( "x" ) )) # Int  |-> ((a_pre + b_pre ) + c_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((((a_pre + b_pre ) + c_pre ) * (((-a_pre) + b_pre ) + c_pre ) ) <= INT_MAX) ”
.

Definition triangle_area_safety_wit_30_split_goal_2 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((b_pre + c_pre ) > a_pre)) (PreH2 : ((a_pre + c_pre ) > b_pre)) (PreH3 : ((a_pre + b_pre ) > c_pre)) (PreH4 : (c_pre > 0)) (PreH5 : (b_pre > 0)) (PreH6 : (a_pre > 0)) (PreH7 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  ((( &( "w" ) )) # Int  |-> ((a_pre + b_pre ) - c_pre ))
  **  ((( &( "z" ) )) # Int  |-> ((a_pre - b_pre ) + c_pre ))
  **  ((( &( "y" ) )) # Int  |-> (((-a_pre) + b_pre ) + c_pre ))
  **  ((( &( "x" ) )) # Int  |-> ((a_pre + b_pre ) + c_pre ))
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((INT_MIN) <= (((a_pre + b_pre ) + c_pre ) * (((-a_pre) + b_pre ) + c_pre ) )) ”
.

Definition triangle_area_return_wit_1 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((b_pre + c_pre ) > a_pre)) (PreH2 : ((a_pre + c_pre ) > b_pre)) (PreH3 : ((a_pre + b_pre ) > c_pre)) (PreH4 : (c_pre > 0)) (PreH5 : (b_pre > 0)) (PreH6 : (a_pre > 0)) (PreH7 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_71_spec_z a_pre b_pre c_pre (((((a_pre + b_pre ) + c_pre ) * (((-a_pre) + b_pre ) + c_pre ) ) * ((a_pre - b_pre ) + c_pre ) ) * ((a_pre + b_pre ) - c_pre ) ) ) ”
  &&  emp
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((b_pre + c_pre ) > a_pre)) (PreH2 : ((a_pre + c_pre ) > b_pre)) (PreH3 : ((a_pre + b_pre ) > c_pre)) (PreH4 : (c_pre > 0)) (PreH5 : (b_pre > 0)) (PreH6 : (a_pre > 0)) (PreH7 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_71_spec_z a_pre b_pre c_pre (((((a_pre + b_pre ) + c_pre ) * (((-a_pre) + b_pre ) + c_pre ) ) * ((a_pre - b_pre ) + c_pre ) ) * ((a_pre + b_pre ) - c_pre ) ) ) ”
  &&  emp
).

Definition triangle_area_return_wit_1_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((b_pre + c_pre ) > a_pre)) (PreH2 : ((a_pre + c_pre ) > b_pre)) (PreH3 : ((a_pre + b_pre ) > c_pre)) (PreH4 : (c_pre > 0)) (PreH5 : (b_pre > 0)) (PreH6 : (a_pre > 0)) (PreH7 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  (problem_71_spec_z a_pre b_pre c_pre (((((a_pre + b_pre ) + c_pre ) * (((-a_pre) + b_pre ) + c_pre ) ) * ((a_pre - b_pre ) + c_pre ) ) * ((a_pre + b_pre ) - c_pre ) ) )
.

Definition triangle_area_return_wit_2 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((a_pre + c_pre ) <= b_pre)) (PreH2 : ((a_pre + b_pre ) > c_pre)) (PreH3 : (c_pre > 0)) (PreH4 : (b_pre > 0)) (PreH5 : (a_pre > 0)) (PreH6 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_71_spec_z a_pre b_pre c_pre (-1) ) ”
  &&  emp
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((a_pre + c_pre ) <= b_pre)) (PreH2 : ((a_pre + b_pre ) > c_pre)) (PreH3 : (c_pre > 0)) (PreH4 : (b_pre > 0)) (PreH5 : (a_pre > 0)) (PreH6 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_71_spec_z a_pre b_pre c_pre (-1) ) ”
  &&  emp
).

Definition triangle_area_return_wit_2_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((a_pre + c_pre ) <= b_pre)) (PreH2 : ((a_pre + b_pre ) > c_pre)) (PreH3 : (c_pre > 0)) (PreH4 : (b_pre > 0)) (PreH5 : (a_pre > 0)) (PreH6 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  (problem_71_spec_z a_pre b_pre c_pre (-1) )
.

Definition triangle_area_return_wit_3 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((a_pre + b_pre ) <= c_pre)) (PreH2 : (c_pre > 0)) (PreH3 : (b_pre > 0)) (PreH4 : (a_pre > 0)) (PreH5 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_71_spec_z a_pre b_pre c_pre (-1) ) ”
  &&  emp
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((a_pre + b_pre ) <= c_pre)) (PreH2 : (c_pre > 0)) (PreH3 : (b_pre > 0)) (PreH4 : (a_pre > 0)) (PreH5 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_71_spec_z a_pre b_pre c_pre (-1) ) ”
  &&  emp
).

Definition triangle_area_return_wit_3_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((a_pre + b_pre ) <= c_pre)) (PreH2 : (c_pre > 0)) (PreH3 : (b_pre > 0)) (PreH4 : (a_pre > 0)) (PreH5 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  (problem_71_spec_z a_pre b_pre c_pre (-1) )
.

Definition triangle_area_return_wit_4 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((b_pre + c_pre ) <= a_pre)) (PreH2 : ((a_pre + c_pre ) > b_pre)) (PreH3 : ((a_pre + b_pre ) > c_pre)) (PreH4 : (c_pre > 0)) (PreH5 : (b_pre > 0)) (PreH6 : (a_pre > 0)) (PreH7 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_71_spec_z a_pre b_pre c_pre (-1) ) ”
  &&  emp
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((b_pre + c_pre ) <= a_pre)) (PreH2 : ((a_pre + c_pre ) > b_pre)) (PreH3 : ((a_pre + b_pre ) > c_pre)) (PreH4 : (c_pre > 0)) (PreH5 : (b_pre > 0)) (PreH6 : (a_pre > 0)) (PreH7 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_71_spec_z a_pre b_pre c_pre (-1) ) ”
  &&  emp
).

Definition triangle_area_return_wit_4_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((b_pre + c_pre ) <= a_pre)) (PreH2 : ((a_pre + c_pre ) > b_pre)) (PreH3 : ((a_pre + b_pre ) > c_pre)) (PreH4 : (c_pre > 0)) (PreH5 : (b_pre > 0)) (PreH6 : (a_pre > 0)) (PreH7 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  (problem_71_spec_z a_pre b_pre c_pre (-1) )
.

Definition triangle_area_return_wit_5 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (b_pre <= 0)) (PreH2 : (a_pre > 0)) (PreH3 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_71_spec_z a_pre b_pre c_pre (-1) ) ”
  &&  emp
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (b_pre <= 0)) (PreH2 : (a_pre > 0)) (PreH3 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_71_spec_z a_pre b_pre c_pre (-1) ) ”
  &&  emp
).

Definition triangle_area_return_wit_5_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (b_pre <= 0)) (PreH2 : (a_pre > 0)) (PreH3 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  (problem_71_spec_z a_pre b_pre c_pre (-1) )
.

Definition triangle_area_return_wit_6 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <= 0)) (PreH2 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_71_spec_z a_pre b_pre c_pre (-1) ) ”
  &&  emp
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <= 0)) (PreH2 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_71_spec_z a_pre b_pre c_pre (-1) ) ”
  &&  emp
).

Definition triangle_area_return_wit_6_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <= 0)) (PreH2 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  (problem_71_spec_z a_pre b_pre c_pre (-1) )
.

Definition triangle_area_return_wit_7 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (c_pre <= 0)) (PreH2 : (b_pre > 0)) (PreH3 : (a_pre > 0)) (PreH4 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_71_spec_z a_pre b_pre c_pre (-1) ) ”
  &&  emp
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (c_pre <= 0)) (PreH2 : (b_pre > 0)) (PreH3 : (a_pre > 0)) (PreH4 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_71_spec_z a_pre b_pre c_pre (-1) ) ”
  &&  emp
).

Definition triangle_area_return_wit_7_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (c_pre <= 0)) (PreH2 : (b_pre > 0)) (PreH3 : (a_pre > 0)) (PreH4 : (problem_71_pre_z a_pre b_pre c_pre )) ,
  (problem_71_spec_z a_pre b_pre c_pre (-1) )
.

Module Type VC_Correct.


Axiom proof_of_triangle_area_safety_wit_1 : triangle_area_safety_wit_1.
Axiom proof_of_triangle_area_safety_wit_2 : triangle_area_safety_wit_2.
Axiom proof_of_triangle_area_safety_wit_3 : triangle_area_safety_wit_3.
Axiom proof_of_triangle_area_safety_wit_4 : triangle_area_safety_wit_4.
Axiom proof_of_triangle_area_safety_wit_5 : triangle_area_safety_wit_5.
Axiom proof_of_triangle_area_safety_wit_6 : triangle_area_safety_wit_6.
Axiom proof_of_triangle_area_safety_wit_7 : triangle_area_safety_wit_7.
Axiom proof_of_triangle_area_safety_wit_8 : triangle_area_safety_wit_8.
Axiom proof_of_triangle_area_safety_wit_9 : triangle_area_safety_wit_9.
Axiom proof_of_triangle_area_safety_wit_10 : triangle_area_safety_wit_10.
Axiom proof_of_triangle_area_safety_wit_11 : triangle_area_safety_wit_11.
Axiom proof_of_triangle_area_safety_wit_12 : triangle_area_safety_wit_12.
Axiom proof_of_triangle_area_safety_wit_13 : triangle_area_safety_wit_13.
Axiom proof_of_triangle_area_safety_wit_14 : triangle_area_safety_wit_14.
Axiom proof_of_triangle_area_safety_wit_15 : triangle_area_safety_wit_15.
Axiom proof_of_triangle_area_safety_wit_16 : triangle_area_safety_wit_16.
Axiom proof_of_triangle_area_safety_wit_17 : triangle_area_safety_wit_17.
Axiom proof_of_triangle_area_safety_wit_18 : triangle_area_safety_wit_18.
Axiom proof_of_triangle_area_safety_wit_19 : triangle_area_safety_wit_19.
Axiom proof_of_triangle_area_safety_wit_20 : triangle_area_safety_wit_20.
Axiom proof_of_triangle_area_safety_wit_21 : triangle_area_safety_wit_21.
Axiom proof_of_triangle_area_safety_wit_22 : triangle_area_safety_wit_22.
Axiom proof_of_triangle_area_safety_wit_23 : triangle_area_safety_wit_23.
Axiom proof_of_triangle_area_safety_wit_24 : triangle_area_safety_wit_24.
Axiom proof_of_triangle_area_safety_wit_25 : triangle_area_safety_wit_25.
Axiom proof_of_triangle_area_safety_wit_26 : triangle_area_safety_wit_26.
Axiom proof_of_triangle_area_safety_wit_27 : triangle_area_safety_wit_27.
Axiom proof_of_triangle_area_safety_wit_28 : triangle_area_safety_wit_28.
Axiom proof_of_triangle_area_safety_wit_29 : triangle_area_safety_wit_29.
Axiom proof_of_triangle_area_safety_wit_30 : triangle_area_safety_wit_30.
Axiom proof_of_triangle_area_return_wit_1 : triangle_area_return_wit_1.
Axiom proof_of_triangle_area_return_wit_2 : triangle_area_return_wit_2.
Axiom proof_of_triangle_area_return_wit_3 : triangle_area_return_wit_3.
Axiom proof_of_triangle_area_return_wit_4 : triangle_area_return_wit_4.
Axiom proof_of_triangle_area_return_wit_5 : triangle_area_return_wit_5.
Axiom proof_of_triangle_area_return_wit_6 : triangle_area_return_wit_6.
Axiom proof_of_triangle_area_return_wit_7 : triangle_area_return_wit_7.

End VC_Correct.
