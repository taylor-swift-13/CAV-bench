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
Require Import p157_right_angle_triangle.
Local Open Scope sac.

(*----- Function right_angle_triangle -----*)

Definition right_angle_triangle_safety_wit_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (0 < a_pre)) (PreH2 : (a_pre <= 32767)) (PreH3 : (0 < b_pre)) (PreH4 : (b_pre <= 32767)) (PreH5 : (0 < c_pre)) (PreH6 : (c_pre <= 32767)) (PreH7 : (problem_157_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((c_pre * c_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (c_pre * c_pre )) ”
.

Definition right_angle_triangle_safety_wit_2 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (0 < a_pre)) (PreH2 : (a_pre <= 32767)) (PreH3 : (0 < b_pre)) (PreH4 : (b_pre <= 32767)) (PreH5 : (0 < c_pre)) (PreH6 : (c_pre <= 32767)) (PreH7 : (problem_157_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (((a_pre * a_pre ) + (b_pre * b_pre ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((a_pre * a_pre ) + (b_pre * b_pre ) )) ”
.

Definition right_angle_triangle_safety_wit_3 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (0 < a_pre)) (PreH2 : (a_pre <= 32767)) (PreH3 : (0 < b_pre)) (PreH4 : (b_pre <= 32767)) (PreH5 : (0 < c_pre)) (PreH6 : (c_pre <= 32767)) (PreH7 : (problem_157_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((b_pre * b_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (b_pre * b_pre )) ”
.

Definition right_angle_triangle_safety_wit_4 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (0 < a_pre)) (PreH2 : (a_pre <= 32767)) (PreH3 : (0 < b_pre)) (PreH4 : (b_pre <= 32767)) (PreH5 : (0 < c_pre)) (PreH6 : (c_pre <= 32767)) (PreH7 : (problem_157_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((a_pre * a_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (a_pre * a_pre )) ”
.

Definition right_angle_triangle_safety_wit_5 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (((a_pre * a_pre ) + (b_pre * b_pre ) ) <> (c_pre * c_pre ))) (PreH2 : (0 < a_pre)) (PreH3 : (a_pre <= 32767)) (PreH4 : (0 < b_pre)) (PreH5 : (b_pre <= 32767)) (PreH6 : (0 < c_pre)) (PreH7 : (c_pre <= 32767)) (PreH8 : (problem_157_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((b_pre * b_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (b_pre * b_pre )) ”
.

Definition right_angle_triangle_safety_wit_6 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (((a_pre * a_pre ) + (b_pre * b_pre ) ) <> (c_pre * c_pre ))) (PreH2 : (0 < a_pre)) (PreH3 : (a_pre <= 32767)) (PreH4 : (0 < b_pre)) (PreH5 : (b_pre <= 32767)) (PreH6 : (0 < c_pre)) (PreH7 : (c_pre <= 32767)) (PreH8 : (problem_157_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (((a_pre * a_pre ) + (c_pre * c_pre ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((a_pre * a_pre ) + (c_pre * c_pre ) )) ”
.

Definition right_angle_triangle_safety_wit_7 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (((a_pre * a_pre ) + (b_pre * b_pre ) ) <> (c_pre * c_pre ))) (PreH2 : (0 < a_pre)) (PreH3 : (a_pre <= 32767)) (PreH4 : (0 < b_pre)) (PreH5 : (b_pre <= 32767)) (PreH6 : (0 < c_pre)) (PreH7 : (c_pre <= 32767)) (PreH8 : (problem_157_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((c_pre * c_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (c_pre * c_pre )) ”
.

Definition right_angle_triangle_safety_wit_8 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (((a_pre * a_pre ) + (b_pre * b_pre ) ) <> (c_pre * c_pre ))) (PreH2 : (0 < a_pre)) (PreH3 : (a_pre <= 32767)) (PreH4 : (0 < b_pre)) (PreH5 : (b_pre <= 32767)) (PreH6 : (0 < c_pre)) (PreH7 : (c_pre <= 32767)) (PreH8 : (problem_157_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((a_pre * a_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (a_pre * a_pre )) ”
.

Definition right_angle_triangle_safety_wit_9 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (((a_pre * a_pre ) + (c_pre * c_pre ) ) <> (b_pre * b_pre ))) (PreH2 : (((a_pre * a_pre ) + (b_pre * b_pre ) ) <> (c_pre * c_pre ))) (PreH3 : (0 < a_pre)) (PreH4 : (a_pre <= 32767)) (PreH5 : (0 < b_pre)) (PreH6 : (b_pre <= 32767)) (PreH7 : (0 < c_pre)) (PreH8 : (c_pre <= 32767)) (PreH9 : (problem_157_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((a_pre * a_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (a_pre * a_pre )) ”
.

Definition right_angle_triangle_safety_wit_10 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (((a_pre * a_pre ) + (c_pre * c_pre ) ) <> (b_pre * b_pre ))) (PreH2 : (((a_pre * a_pre ) + (b_pre * b_pre ) ) <> (c_pre * c_pre ))) (PreH3 : (0 < a_pre)) (PreH4 : (a_pre <= 32767)) (PreH5 : (0 < b_pre)) (PreH6 : (b_pre <= 32767)) (PreH7 : (0 < c_pre)) (PreH8 : (c_pre <= 32767)) (PreH9 : (problem_157_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (((b_pre * b_pre ) + (c_pre * c_pre ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((b_pre * b_pre ) + (c_pre * c_pre ) )) ”
.

Definition right_angle_triangle_safety_wit_11 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (((a_pre * a_pre ) + (c_pre * c_pre ) ) <> (b_pre * b_pre ))) (PreH2 : (((a_pre * a_pre ) + (b_pre * b_pre ) ) <> (c_pre * c_pre ))) (PreH3 : (0 < a_pre)) (PreH4 : (a_pre <= 32767)) (PreH5 : (0 < b_pre)) (PreH6 : (b_pre <= 32767)) (PreH7 : (0 < c_pre)) (PreH8 : (c_pre <= 32767)) (PreH9 : (problem_157_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((c_pre * c_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (c_pre * c_pre )) ”
.

Definition right_angle_triangle_safety_wit_12 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (((a_pre * a_pre ) + (c_pre * c_pre ) ) <> (b_pre * b_pre ))) (PreH2 : (((a_pre * a_pre ) + (b_pre * b_pre ) ) <> (c_pre * c_pre ))) (PreH3 : (0 < a_pre)) (PreH4 : (a_pre <= 32767)) (PreH5 : (0 < b_pre)) (PreH6 : (b_pre <= 32767)) (PreH7 : (0 < c_pre)) (PreH8 : (c_pre <= 32767)) (PreH9 : (problem_157_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((b_pre * b_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (b_pre * b_pre )) ”
.

Definition right_angle_triangle_safety_wit_13 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (((a_pre * a_pre ) + (c_pre * c_pre ) ) = (b_pre * b_pre ))) (PreH2 : (((a_pre * a_pre ) + (b_pre * b_pre ) ) <> (c_pre * c_pre ))) (PreH3 : (0 < a_pre)) (PreH4 : (a_pre <= 32767)) (PreH5 : (0 < b_pre)) (PreH6 : (b_pre <= 32767)) (PreH7 : (0 < c_pre)) (PreH8 : (c_pre <= 32767)) (PreH9 : (problem_157_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition right_angle_triangle_safety_wit_14 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (((a_pre * a_pre ) + (b_pre * b_pre ) ) = (c_pre * c_pre ))) (PreH2 : (0 < a_pre)) (PreH3 : (a_pre <= 32767)) (PreH4 : (0 < b_pre)) (PreH5 : (b_pre <= 32767)) (PreH6 : (0 < c_pre)) (PreH7 : (c_pre <= 32767)) (PreH8 : (problem_157_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition right_angle_triangle_safety_wit_15 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (((b_pre * b_pre ) + (c_pre * c_pre ) ) = (a_pre * a_pre ))) (PreH2 : (((a_pre * a_pre ) + (c_pre * c_pre ) ) <> (b_pre * b_pre ))) (PreH3 : (((a_pre * a_pre ) + (b_pre * b_pre ) ) <> (c_pre * c_pre ))) (PreH4 : (0 < a_pre)) (PreH5 : (a_pre <= 32767)) (PreH6 : (0 < b_pre)) (PreH7 : (b_pre <= 32767)) (PreH8 : (0 < c_pre)) (PreH9 : (c_pre <= 32767)) (PreH10 : (problem_157_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition right_angle_triangle_safety_wit_16 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (((b_pre * b_pre ) + (c_pre * c_pre ) ) <> (a_pre * a_pre ))) (PreH2 : (((a_pre * a_pre ) + (c_pre * c_pre ) ) <> (b_pre * b_pre ))) (PreH3 : (((a_pre * a_pre ) + (b_pre * b_pre ) ) <> (c_pre * c_pre ))) (PreH4 : (0 < a_pre)) (PreH5 : (a_pre <= 32767)) (PreH6 : (0 < b_pre)) (PreH7 : (b_pre <= 32767)) (PreH8 : (0 < c_pre)) (PreH9 : (c_pre <= 32767)) (PreH10 : (problem_157_pre_z a_pre b_pre c_pre )) ,
  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition right_angle_triangle_return_wit_1 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (((b_pre * b_pre ) + (c_pre * c_pre ) ) <> (a_pre * a_pre ))) (PreH2 : (((a_pre * a_pre ) + (c_pre * c_pre ) ) <> (b_pre * b_pre ))) (PreH3 : (((a_pre * a_pre ) + (b_pre * b_pre ) ) <> (c_pre * c_pre ))) (PreH4 : (0 < a_pre)) (PreH5 : (a_pre <= 32767)) (PreH6 : (0 < b_pre)) (PreH7 : (b_pre <= 32767)) (PreH8 : (0 < c_pre)) (PreH9 : (c_pre <= 32767)) (PreH10 : (problem_157_pre_z a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_157_spec_z a_pre b_pre c_pre 0 ) ”
  &&  emp
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (((b_pre * b_pre ) + (c_pre * c_pre ) ) <> (a_pre * a_pre ))) (PreH2 : (((a_pre * a_pre ) + (c_pre * c_pre ) ) <> (b_pre * b_pre ))) (PreH3 : (((a_pre * a_pre ) + (b_pre * b_pre ) ) <> (c_pre * c_pre ))) (PreH4 : (0 < a_pre)) (PreH5 : (a_pre <= 32767)) (PreH6 : (0 < b_pre)) (PreH7 : (b_pre <= 32767)) (PreH8 : (0 < c_pre)) (PreH9 : (c_pre <= 32767)) (PreH10 : (problem_157_pre_z a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_157_spec_z a_pre b_pre c_pre 0 ) ”
  &&  emp
).

Definition right_angle_triangle_return_wit_1_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (((b_pre * b_pre ) + (c_pre * c_pre ) ) <> (a_pre * a_pre ))) (PreH2 : (((a_pre * a_pre ) + (c_pre * c_pre ) ) <> (b_pre * b_pre ))) (PreH3 : (((a_pre * a_pre ) + (b_pre * b_pre ) ) <> (c_pre * c_pre ))) (PreH4 : (0 < a_pre)) (PreH5 : (a_pre <= 32767)) (PreH6 : (0 < b_pre)) (PreH7 : (b_pre <= 32767)) (PreH8 : (0 < c_pre)) (PreH9 : (c_pre <= 32767)) (PreH10 : (problem_157_pre_z a_pre b_pre c_pre )) ,
  (problem_157_spec_z a_pre b_pre c_pre 0 )
.

Definition right_angle_triangle_return_wit_2 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (((a_pre * a_pre ) + (c_pre * c_pre ) ) = (b_pre * b_pre ))) (PreH2 : (((a_pre * a_pre ) + (b_pre * b_pre ) ) <> (c_pre * c_pre ))) (PreH3 : (0 < a_pre)) (PreH4 : (a_pre <= 32767)) (PreH5 : (0 < b_pre)) (PreH6 : (b_pre <= 32767)) (PreH7 : (0 < c_pre)) (PreH8 : (c_pre <= 32767)) (PreH9 : (problem_157_pre_z a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_157_spec_z a_pre b_pre c_pre 1 ) ”
  &&  emp
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (((a_pre * a_pre ) + (c_pre * c_pre ) ) = (b_pre * b_pre ))) (PreH2 : (((a_pre * a_pre ) + (b_pre * b_pre ) ) <> (c_pre * c_pre ))) (PreH3 : (0 < a_pre)) (PreH4 : (a_pre <= 32767)) (PreH5 : (0 < b_pre)) (PreH6 : (b_pre <= 32767)) (PreH7 : (0 < c_pre)) (PreH8 : (c_pre <= 32767)) (PreH9 : (problem_157_pre_z a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_157_spec_z a_pre b_pre c_pre 1 ) ”
  &&  emp
).

Definition right_angle_triangle_return_wit_2_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (((a_pre * a_pre ) + (c_pre * c_pre ) ) = (b_pre * b_pre ))) (PreH2 : (((a_pre * a_pre ) + (b_pre * b_pre ) ) <> (c_pre * c_pre ))) (PreH3 : (0 < a_pre)) (PreH4 : (a_pre <= 32767)) (PreH5 : (0 < b_pre)) (PreH6 : (b_pre <= 32767)) (PreH7 : (0 < c_pre)) (PreH8 : (c_pre <= 32767)) (PreH9 : (problem_157_pre_z a_pre b_pre c_pre )) ,
  (problem_157_spec_z a_pre b_pre c_pre 1 )
.

Definition right_angle_triangle_return_wit_3 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (((a_pre * a_pre ) + (b_pre * b_pre ) ) = (c_pre * c_pre ))) (PreH2 : (0 < a_pre)) (PreH3 : (a_pre <= 32767)) (PreH4 : (0 < b_pre)) (PreH5 : (b_pre <= 32767)) (PreH6 : (0 < c_pre)) (PreH7 : (c_pre <= 32767)) (PreH8 : (problem_157_pre_z a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_157_spec_z a_pre b_pre c_pre 1 ) ”
  &&  emp
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (((a_pre * a_pre ) + (b_pre * b_pre ) ) = (c_pre * c_pre ))) (PreH2 : (0 < a_pre)) (PreH3 : (a_pre <= 32767)) (PreH4 : (0 < b_pre)) (PreH5 : (b_pre <= 32767)) (PreH6 : (0 < c_pre)) (PreH7 : (c_pre <= 32767)) (PreH8 : (problem_157_pre_z a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_157_spec_z a_pre b_pre c_pre 1 ) ”
  &&  emp
).

Definition right_angle_triangle_return_wit_3_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (((a_pre * a_pre ) + (b_pre * b_pre ) ) = (c_pre * c_pre ))) (PreH2 : (0 < a_pre)) (PreH3 : (a_pre <= 32767)) (PreH4 : (0 < b_pre)) (PreH5 : (b_pre <= 32767)) (PreH6 : (0 < c_pre)) (PreH7 : (c_pre <= 32767)) (PreH8 : (problem_157_pre_z a_pre b_pre c_pre )) ,
  (problem_157_spec_z a_pre b_pre c_pre 1 )
.

Definition right_angle_triangle_return_wit_4 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (((b_pre * b_pre ) + (c_pre * c_pre ) ) = (a_pre * a_pre ))) (PreH2 : (((a_pre * a_pre ) + (c_pre * c_pre ) ) <> (b_pre * b_pre ))) (PreH3 : (((a_pre * a_pre ) + (b_pre * b_pre ) ) <> (c_pre * c_pre ))) (PreH4 : (0 < a_pre)) (PreH5 : (a_pre <= 32767)) (PreH6 : (0 < b_pre)) (PreH7 : (b_pre <= 32767)) (PreH8 : (0 < c_pre)) (PreH9 : (c_pre <= 32767)) (PreH10 : (problem_157_pre_z a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_157_spec_z a_pre b_pre c_pre 1 ) ”
  &&  emp
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (((b_pre * b_pre ) + (c_pre * c_pre ) ) = (a_pre * a_pre ))) (PreH2 : (((a_pre * a_pre ) + (c_pre * c_pre ) ) <> (b_pre * b_pre ))) (PreH3 : (((a_pre * a_pre ) + (b_pre * b_pre ) ) <> (c_pre * c_pre ))) (PreH4 : (0 < a_pre)) (PreH5 : (a_pre <= 32767)) (PreH6 : (0 < b_pre)) (PreH7 : (b_pre <= 32767)) (PreH8 : (0 < c_pre)) (PreH9 : (c_pre <= 32767)) (PreH10 : (problem_157_pre_z a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_157_spec_z a_pre b_pre c_pre 1 ) ”
  &&  emp
).

Definition right_angle_triangle_return_wit_4_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (((b_pre * b_pre ) + (c_pre * c_pre ) ) = (a_pre * a_pre ))) (PreH2 : (((a_pre * a_pre ) + (c_pre * c_pre ) ) <> (b_pre * b_pre ))) (PreH3 : (((a_pre * a_pre ) + (b_pre * b_pre ) ) <> (c_pre * c_pre ))) (PreH4 : (0 < a_pre)) (PreH5 : (a_pre <= 32767)) (PreH6 : (0 < b_pre)) (PreH7 : (b_pre <= 32767)) (PreH8 : (0 < c_pre)) (PreH9 : (c_pre <= 32767)) (PreH10 : (problem_157_pre_z a_pre b_pre c_pre )) ,
  (problem_157_spec_z a_pre b_pre c_pre 1 )
.

Module Type VC_Correct.


Axiom proof_of_right_angle_triangle_safety_wit_1 : right_angle_triangle_safety_wit_1.
Axiom proof_of_right_angle_triangle_safety_wit_2 : right_angle_triangle_safety_wit_2.
Axiom proof_of_right_angle_triangle_safety_wit_3 : right_angle_triangle_safety_wit_3.
Axiom proof_of_right_angle_triangle_safety_wit_4 : right_angle_triangle_safety_wit_4.
Axiom proof_of_right_angle_triangle_safety_wit_5 : right_angle_triangle_safety_wit_5.
Axiom proof_of_right_angle_triangle_safety_wit_6 : right_angle_triangle_safety_wit_6.
Axiom proof_of_right_angle_triangle_safety_wit_7 : right_angle_triangle_safety_wit_7.
Axiom proof_of_right_angle_triangle_safety_wit_8 : right_angle_triangle_safety_wit_8.
Axiom proof_of_right_angle_triangle_safety_wit_9 : right_angle_triangle_safety_wit_9.
Axiom proof_of_right_angle_triangle_safety_wit_10 : right_angle_triangle_safety_wit_10.
Axiom proof_of_right_angle_triangle_safety_wit_11 : right_angle_triangle_safety_wit_11.
Axiom proof_of_right_angle_triangle_safety_wit_12 : right_angle_triangle_safety_wit_12.
Axiom proof_of_right_angle_triangle_safety_wit_13 : right_angle_triangle_safety_wit_13.
Axiom proof_of_right_angle_triangle_safety_wit_14 : right_angle_triangle_safety_wit_14.
Axiom proof_of_right_angle_triangle_safety_wit_15 : right_angle_triangle_safety_wit_15.
Axiom proof_of_right_angle_triangle_safety_wit_16 : right_angle_triangle_safety_wit_16.
Axiom proof_of_right_angle_triangle_return_wit_1 : right_angle_triangle_return_wit_1.
Axiom proof_of_right_angle_triangle_return_wit_2 : right_angle_triangle_return_wit_2.
Axiom proof_of_right_angle_triangle_return_wit_3 : right_angle_triangle_return_wit_3.
Axiom proof_of_right_angle_triangle_return_wit_4 : right_angle_triangle_return_wit_4.

End VC_Correct.
