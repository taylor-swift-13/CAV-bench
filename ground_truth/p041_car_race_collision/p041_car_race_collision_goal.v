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
Require Import p041_car_race_collision.
Local Open Scope sac.

(*----- Function car_race_collision -----*)

Definition car_race_collision_safety_wit_1 :=
(
forall (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : ((n_pre * n_pre ) <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((n_pre * n_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n_pre * n_pre )) ”
) \/
(
forall (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : ((n_pre * n_pre ) <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((n_pre * n_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n_pre * n_pre )) ”
).

Definition car_race_collision_safety_wit_1_split_goal_1 :=
forall (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : ((n_pre * n_pre ) <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((n_pre * n_pre ) <= INT_MAX) ”
.

Definition car_race_collision_safety_wit_1_split_goal_2 :=
forall (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : ((n_pre * n_pre ) <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((INT_MIN) <= (n_pre * n_pre )) ”
.

Definition car_race_collision_return_wit_1 :=
(
forall (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : ((n_pre * n_pre ) <= INT_MAX)) ,
  TT && emp
|--
  “ (problem_41_spec_z n_pre (n_pre * n_pre ) ) ”
  &&  emp
) \/
(
forall (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : ((n_pre * n_pre ) <= INT_MAX)) ,
  TT && emp
|--
  “ (problem_41_spec_z n_pre (n_pre * n_pre ) ) ”
  &&  emp
).

Definition car_race_collision_return_wit_1_split_goal_1 :=
forall (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : ((n_pre * n_pre ) <= INT_MAX)) ,
  TT && emp
|--
  “ (problem_41_spec_z n_pre (n_pre * n_pre ) ) ”
.

Module Type VC_Correct.


Axiom proof_of_car_race_collision_safety_wit_1 : car_race_collision_safety_wit_1.
Axiom proof_of_car_race_collision_return_wit_1 : car_race_collision_return_wit_1.

End VC_Correct.
