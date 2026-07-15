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
Require Import p092_any_int.
Local Open Scope sac.

(*----- Function any_int -----*)

Definition any_int_safety_wit_1 := 
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  ((( &( "c_is_int" ) )) # Int  |-> c_is_int_pre)
  **  ((( &( "b_is_int" ) )) # Int  |-> b_is_int_pre)
  **  ((( &( "a_is_int" ) )) # Int  |-> a_is_int_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition any_int_safety_wit_2 := 
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_is_int_pre = 0)) (PreH2 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  ((( &( "c_is_int" ) )) # Int  |-> c_is_int_pre)
  **  ((( &( "b_is_int" ) )) # Int  |-> b_is_int_pre)
  **  ((( &( "a_is_int" ) )) # Int  |-> a_is_int_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition any_int_safety_wit_3 := 
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_is_int_pre <> 0)) (PreH2 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  ((( &( "c_is_int" ) )) # Int  |-> c_is_int_pre)
  **  ((( &( "b_is_int" ) )) # Int  |-> b_is_int_pre)
  **  ((( &( "a_is_int" ) )) # Int  |-> a_is_int_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition any_int_safety_wit_4 := 
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (b_is_int_pre = 0)) (PreH2 : (a_is_int_pre <> 0)) (PreH3 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  ((( &( "c_is_int" ) )) # Int  |-> c_is_int_pre)
  **  ((( &( "b_is_int" ) )) # Int  |-> b_is_int_pre)
  **  ((( &( "a_is_int" ) )) # Int  |-> a_is_int_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition any_int_safety_wit_5 := 
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (b_is_int_pre <> 0)) (PreH2 : (a_is_int_pre <> 0)) (PreH3 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  ((( &( "c_is_int" ) )) # Int  |-> c_is_int_pre)
  **  ((( &( "b_is_int" ) )) # Int  |-> b_is_int_pre)
  **  ((( &( "a_is_int" ) )) # Int  |-> a_is_int_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition any_int_safety_wit_6 := 
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (c_is_int_pre = 0)) (PreH2 : (b_is_int_pre <> 0)) (PreH3 : (a_is_int_pre <> 0)) (PreH4 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  ((( &( "c_is_int" ) )) # Int  |-> c_is_int_pre)
  **  ((( &( "b_is_int" ) )) # Int  |-> b_is_int_pre)
  **  ((( &( "a_is_int" ) )) # Int  |-> a_is_int_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition any_int_safety_wit_7 := 
(
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (c_is_int_pre <> 0)) (PreH2 : (b_is_int_pre <> 0)) (PreH3 : (a_is_int_pre <> 0)) (PreH4 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  ((( &( "c_is_int" ) )) # Int  |-> c_is_int_pre)
  **  ((( &( "b_is_int" ) )) # Int  |-> b_is_int_pre)
  **  ((( &( "a_is_int" ) )) # Int  |-> a_is_int_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((b_pre + c_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (b_pre + c_pre )) ”
) \/
(
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (c_is_int_pre <> 0)) (PreH2 : (b_is_int_pre <> 0)) (PreH3 : (a_is_int_pre <> 0)) (PreH4 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  ((( &( "c_is_int" ) )) # Int  |-> c_is_int_pre)
  **  ((( &( "b_is_int" ) )) # Int  |-> b_is_int_pre)
  **  ((( &( "a_is_int" ) )) # Int  |-> a_is_int_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((b_pre + c_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (b_pre + c_pre )) ”
).

Definition any_int_safety_wit_7_split_goal_1 := 
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (c_is_int_pre <> 0)) (PreH2 : (b_is_int_pre <> 0)) (PreH3 : (a_is_int_pre <> 0)) (PreH4 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  ((( &( "c_is_int" ) )) # Int  |-> c_is_int_pre)
  **  ((( &( "b_is_int" ) )) # Int  |-> b_is_int_pre)
  **  ((( &( "a_is_int" ) )) # Int  |-> a_is_int_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((b_pre + c_pre ) <= INT_MAX) ”
.

Definition any_int_safety_wit_7_split_goal_2 := 
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (c_is_int_pre <> 0)) (PreH2 : (b_is_int_pre <> 0)) (PreH3 : (a_is_int_pre <> 0)) (PreH4 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  ((( &( "c_is_int" ) )) # Int  |-> c_is_int_pre)
  **  ((( &( "b_is_int" ) )) # Int  |-> b_is_int_pre)
  **  ((( &( "a_is_int" ) )) # Int  |-> a_is_int_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((INT_MIN) <= (b_pre + c_pre )) ”
.

Definition any_int_safety_wit_8 := 
(
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <> (b_pre + c_pre ))) (PreH2 : (c_is_int_pre <> 0)) (PreH3 : (b_is_int_pre <> 0)) (PreH4 : (a_is_int_pre <> 0)) (PreH5 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  ((( &( "c_is_int" ) )) # Int  |-> c_is_int_pre)
  **  ((( &( "b_is_int" ) )) # Int  |-> b_is_int_pre)
  **  ((( &( "a_is_int" ) )) # Int  |-> a_is_int_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((a_pre + c_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (a_pre + c_pre )) ”
) \/
(
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <> (b_pre + c_pre ))) (PreH2 : (c_is_int_pre <> 0)) (PreH3 : (b_is_int_pre <> 0)) (PreH4 : (a_is_int_pre <> 0)) (PreH5 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  ((( &( "c_is_int" ) )) # Int  |-> c_is_int_pre)
  **  ((( &( "b_is_int" ) )) # Int  |-> b_is_int_pre)
  **  ((( &( "a_is_int" ) )) # Int  |-> a_is_int_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((a_pre + c_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (a_pre + c_pre )) ”
).

Definition any_int_safety_wit_8_split_goal_1 := 
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <> (b_pre + c_pre ))) (PreH2 : (c_is_int_pre <> 0)) (PreH3 : (b_is_int_pre <> 0)) (PreH4 : (a_is_int_pre <> 0)) (PreH5 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  ((( &( "c_is_int" ) )) # Int  |-> c_is_int_pre)
  **  ((( &( "b_is_int" ) )) # Int  |-> b_is_int_pre)
  **  ((( &( "a_is_int" ) )) # Int  |-> a_is_int_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((a_pre + c_pre ) <= INT_MAX) ”
.

Definition any_int_safety_wit_8_split_goal_2 := 
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <> (b_pre + c_pre ))) (PreH2 : (c_is_int_pre <> 0)) (PreH3 : (b_is_int_pre <> 0)) (PreH4 : (a_is_int_pre <> 0)) (PreH5 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  ((( &( "c_is_int" ) )) # Int  |-> c_is_int_pre)
  **  ((( &( "b_is_int" ) )) # Int  |-> b_is_int_pre)
  **  ((( &( "a_is_int" ) )) # Int  |-> a_is_int_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((INT_MIN) <= (a_pre + c_pre )) ”
.

Definition any_int_safety_wit_9 := 
(
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (b_pre <> (a_pre + c_pre ))) (PreH2 : (a_pre <> (b_pre + c_pre ))) (PreH3 : (c_is_int_pre <> 0)) (PreH4 : (b_is_int_pre <> 0)) (PreH5 : (a_is_int_pre <> 0)) (PreH6 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  ((( &( "c_is_int" ) )) # Int  |-> c_is_int_pre)
  **  ((( &( "b_is_int" ) )) # Int  |-> b_is_int_pre)
  **  ((( &( "a_is_int" ) )) # Int  |-> a_is_int_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((a_pre + b_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (a_pre + b_pre )) ”
) \/
(
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (b_pre <> (a_pre + c_pre ))) (PreH2 : (a_pre <> (b_pre + c_pre ))) (PreH3 : (c_is_int_pre <> 0)) (PreH4 : (b_is_int_pre <> 0)) (PreH5 : (a_is_int_pre <> 0)) (PreH6 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  ((( &( "c_is_int" ) )) # Int  |-> c_is_int_pre)
  **  ((( &( "b_is_int" ) )) # Int  |-> b_is_int_pre)
  **  ((( &( "a_is_int" ) )) # Int  |-> a_is_int_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((a_pre + b_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (a_pre + b_pre )) ”
).

Definition any_int_safety_wit_9_split_goal_1 := 
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (b_pre <> (a_pre + c_pre ))) (PreH2 : (a_pre <> (b_pre + c_pre ))) (PreH3 : (c_is_int_pre <> 0)) (PreH4 : (b_is_int_pre <> 0)) (PreH5 : (a_is_int_pre <> 0)) (PreH6 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  ((( &( "c_is_int" ) )) # Int  |-> c_is_int_pre)
  **  ((( &( "b_is_int" ) )) # Int  |-> b_is_int_pre)
  **  ((( &( "a_is_int" ) )) # Int  |-> a_is_int_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((a_pre + b_pre ) <= INT_MAX) ”
.

Definition any_int_safety_wit_9_split_goal_2 := 
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (b_pre <> (a_pre + c_pre ))) (PreH2 : (a_pre <> (b_pre + c_pre ))) (PreH3 : (c_is_int_pre <> 0)) (PreH4 : (b_is_int_pre <> 0)) (PreH5 : (a_is_int_pre <> 0)) (PreH6 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  ((( &( "c_is_int" ) )) # Int  |-> c_is_int_pre)
  **  ((( &( "b_is_int" ) )) # Int  |-> b_is_int_pre)
  **  ((( &( "a_is_int" ) )) # Int  |-> a_is_int_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((INT_MIN) <= (a_pre + b_pre )) ”
.

Definition any_int_safety_wit_10 := 
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (b_pre = (a_pre + c_pre ))) (PreH2 : (a_pre <> (b_pre + c_pre ))) (PreH3 : (c_is_int_pre <> 0)) (PreH4 : (b_is_int_pre <> 0)) (PreH5 : (a_is_int_pre <> 0)) (PreH6 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  ((( &( "c_is_int" ) )) # Int  |-> c_is_int_pre)
  **  ((( &( "b_is_int" ) )) # Int  |-> b_is_int_pre)
  **  ((( &( "a_is_int" ) )) # Int  |-> a_is_int_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition any_int_safety_wit_11 := 
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre = (b_pre + c_pre ))) (PreH2 : (c_is_int_pre <> 0)) (PreH3 : (b_is_int_pre <> 0)) (PreH4 : (a_is_int_pre <> 0)) (PreH5 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  ((( &( "c_is_int" ) )) # Int  |-> c_is_int_pre)
  **  ((( &( "b_is_int" ) )) # Int  |-> b_is_int_pre)
  **  ((( &( "a_is_int" ) )) # Int  |-> a_is_int_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition any_int_safety_wit_12 := 
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (c_pre = (a_pre + b_pre ))) (PreH2 : (b_pre <> (a_pre + c_pre ))) (PreH3 : (a_pre <> (b_pre + c_pre ))) (PreH4 : (c_is_int_pre <> 0)) (PreH5 : (b_is_int_pre <> 0)) (PreH6 : (a_is_int_pre <> 0)) (PreH7 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  ((( &( "c_is_int" ) )) # Int  |-> c_is_int_pre)
  **  ((( &( "b_is_int" ) )) # Int  |-> b_is_int_pre)
  **  ((( &( "a_is_int" ) )) # Int  |-> a_is_int_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition any_int_safety_wit_13 := 
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (c_pre <> (a_pre + b_pre ))) (PreH2 : (b_pre <> (a_pre + c_pre ))) (PreH3 : (a_pre <> (b_pre + c_pre ))) (PreH4 : (c_is_int_pre <> 0)) (PreH5 : (b_is_int_pre <> 0)) (PreH6 : (a_is_int_pre <> 0)) (PreH7 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  ((( &( "c_is_int" ) )) # Int  |-> c_is_int_pre)
  **  ((( &( "b_is_int" ) )) # Int  |-> b_is_int_pre)
  **  ((( &( "a_is_int" ) )) # Int  |-> a_is_int_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition any_int_return_wit_1 := 
(
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (c_pre <> (a_pre + b_pre ))) (PreH2 : (b_pre <> (a_pre + c_pre ))) (PreH3 : (a_pre <> (b_pre + c_pre ))) (PreH4 : (c_is_int_pre <> 0)) (PreH5 : (b_is_int_pre <> 0)) (PreH6 : (a_is_int_pre <> 0)) (PreH7 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  TT && emp 
|--
  “ (problem_92_spec_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre 0 ) ”
  &&  emp
) \/
(
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (c_pre <> (a_pre + b_pre ))) (PreH2 : (b_pre <> (a_pre + c_pre ))) (PreH3 : (a_pre <> (b_pre + c_pre ))) (PreH4 : (c_is_int_pre <> 0)) (PreH5 : (b_is_int_pre <> 0)) (PreH6 : (a_is_int_pre <> 0)) (PreH7 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  TT && emp 
|--
  “ (problem_92_spec_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre 0 ) ”
  &&  emp
).

Definition any_int_return_wit_1_split_goal_1 := 
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (c_pre <> (a_pre + b_pre ))) (PreH2 : (b_pre <> (a_pre + c_pre ))) (PreH3 : (a_pre <> (b_pre + c_pre ))) (PreH4 : (c_is_int_pre <> 0)) (PreH5 : (b_is_int_pre <> 0)) (PreH6 : (a_is_int_pre <> 0)) (PreH7 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  (problem_92_spec_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre 0 )
.

Definition any_int_return_wit_2 := 
(
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (b_pre = (a_pre + c_pre ))) (PreH2 : (a_pre <> (b_pre + c_pre ))) (PreH3 : (c_is_int_pre <> 0)) (PreH4 : (b_is_int_pre <> 0)) (PreH5 : (a_is_int_pre <> 0)) (PreH6 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  TT && emp 
|--
  “ (problem_92_spec_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre 1 ) ”
  &&  emp
) \/
(
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (b_pre = (a_pre + c_pre ))) (PreH2 : (a_pre <> (b_pre + c_pre ))) (PreH3 : (c_is_int_pre <> 0)) (PreH4 : (b_is_int_pre <> 0)) (PreH5 : (a_is_int_pre <> 0)) (PreH6 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  TT && emp 
|--
  “ (problem_92_spec_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre 1 ) ”
  &&  emp
).

Definition any_int_return_wit_2_split_goal_1 := 
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (b_pre = (a_pre + c_pre ))) (PreH2 : (a_pre <> (b_pre + c_pre ))) (PreH3 : (c_is_int_pre <> 0)) (PreH4 : (b_is_int_pre <> 0)) (PreH5 : (a_is_int_pre <> 0)) (PreH6 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  (problem_92_spec_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre 1 )
.

Definition any_int_return_wit_3 := 
(
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre = (b_pre + c_pre ))) (PreH2 : (c_is_int_pre <> 0)) (PreH3 : (b_is_int_pre <> 0)) (PreH4 : (a_is_int_pre <> 0)) (PreH5 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  TT && emp 
|--
  “ (problem_92_spec_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre 1 ) ”
  &&  emp
) \/
(
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre = (b_pre + c_pre ))) (PreH2 : (c_is_int_pre <> 0)) (PreH3 : (b_is_int_pre <> 0)) (PreH4 : (a_is_int_pre <> 0)) (PreH5 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  TT && emp 
|--
  “ (problem_92_spec_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre 1 ) ”
  &&  emp
).

Definition any_int_return_wit_3_split_goal_1 := 
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre = (b_pre + c_pre ))) (PreH2 : (c_is_int_pre <> 0)) (PreH3 : (b_is_int_pre <> 0)) (PreH4 : (a_is_int_pre <> 0)) (PreH5 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  (problem_92_spec_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre 1 )
.

Definition any_int_return_wit_4 := 
(
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (c_pre = (a_pre + b_pre ))) (PreH2 : (b_pre <> (a_pre + c_pre ))) (PreH3 : (a_pre <> (b_pre + c_pre ))) (PreH4 : (c_is_int_pre <> 0)) (PreH5 : (b_is_int_pre <> 0)) (PreH6 : (a_is_int_pre <> 0)) (PreH7 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  TT && emp 
|--
  “ (problem_92_spec_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre 1 ) ”
  &&  emp
) \/
(
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (c_pre = (a_pre + b_pre ))) (PreH2 : (b_pre <> (a_pre + c_pre ))) (PreH3 : (a_pre <> (b_pre + c_pre ))) (PreH4 : (c_is_int_pre <> 0)) (PreH5 : (b_is_int_pre <> 0)) (PreH6 : (a_is_int_pre <> 0)) (PreH7 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  TT && emp 
|--
  “ (problem_92_spec_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre 1 ) ”
  &&  emp
).

Definition any_int_return_wit_4_split_goal_1 := 
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (c_pre = (a_pre + b_pre ))) (PreH2 : (b_pre <> (a_pre + c_pre ))) (PreH3 : (a_pre <> (b_pre + c_pre ))) (PreH4 : (c_is_int_pre <> 0)) (PreH5 : (b_is_int_pre <> 0)) (PreH6 : (a_is_int_pre <> 0)) (PreH7 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  (problem_92_spec_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre 1 )
.

Definition any_int_return_wit_5 := 
(
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (c_is_int_pre = 0)) (PreH2 : (b_is_int_pre <> 0)) (PreH3 : (a_is_int_pre <> 0)) (PreH4 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  TT && emp 
|--
  “ (problem_92_spec_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre 0 ) ”
  &&  emp
) \/
(
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (c_is_int_pre = 0)) (PreH2 : (b_is_int_pre <> 0)) (PreH3 : (a_is_int_pre <> 0)) (PreH4 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  TT && emp 
|--
  “ (problem_92_spec_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre 0 ) ”
  &&  emp
).

Definition any_int_return_wit_5_split_goal_1 := 
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (c_is_int_pre = 0)) (PreH2 : (b_is_int_pre <> 0)) (PreH3 : (a_is_int_pre <> 0)) (PreH4 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  (problem_92_spec_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre 0 )
.

Definition any_int_return_wit_6 := 
(
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (b_is_int_pre = 0)) (PreH2 : (a_is_int_pre <> 0)) (PreH3 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  TT && emp 
|--
  “ (problem_92_spec_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre 0 ) ”
  &&  emp
) \/
(
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (b_is_int_pre = 0)) (PreH2 : (a_is_int_pre <> 0)) (PreH3 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  TT && emp 
|--
  “ (problem_92_spec_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre 0 ) ”
  &&  emp
).

Definition any_int_return_wit_6_split_goal_1 := 
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (b_is_int_pre = 0)) (PreH2 : (a_is_int_pre <> 0)) (PreH3 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  (problem_92_spec_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre 0 )
.

Definition any_int_return_wit_7 := 
(
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_is_int_pre = 0)) (PreH2 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  TT && emp 
|--
  “ (problem_92_spec_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre 0 ) ”
  &&  emp
) \/
(
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_is_int_pre = 0)) (PreH2 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  TT && emp 
|--
  “ (problem_92_spec_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre 0 ) ”
  &&  emp
).

Definition any_int_return_wit_7_split_goal_1 := 
forall (c_is_int_pre: Z) (b_is_int_pre: Z) (a_is_int_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_is_int_pre = 0)) (PreH2 : (problem_92_pre_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre )) ,
  (problem_92_spec_z a_pre b_pre c_pre a_is_int_pre b_is_int_pre c_is_int_pre 0 )
.

Module Type VC_Correct.


Axiom proof_of_any_int_safety_wit_1 : any_int_safety_wit_1.
Axiom proof_of_any_int_safety_wit_2 : any_int_safety_wit_2.
Axiom proof_of_any_int_safety_wit_3 : any_int_safety_wit_3.
Axiom proof_of_any_int_safety_wit_4 : any_int_safety_wit_4.
Axiom proof_of_any_int_safety_wit_5 : any_int_safety_wit_5.
Axiom proof_of_any_int_safety_wit_6 : any_int_safety_wit_6.
Axiom proof_of_any_int_safety_wit_7 : any_int_safety_wit_7.
Axiom proof_of_any_int_safety_wit_8 : any_int_safety_wit_8.
Axiom proof_of_any_int_safety_wit_9 : any_int_safety_wit_9.
Axiom proof_of_any_int_safety_wit_10 : any_int_safety_wit_10.
Axiom proof_of_any_int_safety_wit_11 : any_int_safety_wit_11.
Axiom proof_of_any_int_safety_wit_12 : any_int_safety_wit_12.
Axiom proof_of_any_int_safety_wit_13 : any_int_safety_wit_13.
Axiom proof_of_any_int_return_wit_1 : any_int_return_wit_1.
Axiom proof_of_any_int_return_wit_2 : any_int_return_wit_2.
Axiom proof_of_any_int_return_wit_3 : any_int_return_wit_3.
Axiom proof_of_any_int_return_wit_4 : any_int_return_wit_4.
Axiom proof_of_any_int_return_wit_5 : any_int_return_wit_5.
Axiom proof_of_any_int_return_wit_6 : any_int_return_wit_6.
Axiom proof_of_any_int_return_wit_7 : any_int_return_wit_7.

End VC_Correct.
