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
Require Import p045_triangle_area.
Local Open Scope sac.

(*----- Function triangle_area -----*)

Definition triangle_area_safety_wit_1 := 
forall (h_pre: Z) (a_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 46340)) (PreH3 : (0 <= h_pre)) (PreH4 : (h_pre <= 46340)) (PreH5 : (problem_45_pre_z a_pre h_pre )) ,
  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((a_pre * h_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (a_pre * h_pre )) ”
.

Definition triangle_area_return_wit_1 := 
(
forall (h_pre: Z) (a_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 46340)) (PreH3 : (0 <= h_pre)) (PreH4 : (h_pre <= 46340)) (PreH5 : (problem_45_pre_z a_pre h_pre )) ,
  TT && emp 
|--
  “ (problem_45_spec_twice_z a_pre h_pre (a_pre * h_pre ) ) ”
  &&  emp
) \/
(
forall (h_pre: Z) (a_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 46340)) (PreH3 : (0 <= h_pre)) (PreH4 : (h_pre <= 46340)) (PreH5 : (problem_45_pre_z a_pre h_pre )) ,
  TT && emp 
|--
  “ (problem_45_spec_twice_z a_pre h_pre (a_pre * h_pre ) ) ”
  &&  emp
).

Definition triangle_area_return_wit_1_split_goal_1 := 
forall (h_pre: Z) (a_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 46340)) (PreH3 : (0 <= h_pre)) (PreH4 : (h_pre <= 46340)) (PreH5 : (problem_45_pre_z a_pre h_pre )) ,
  (problem_45_spec_twice_z a_pre h_pre (a_pre * h_pre ) )
.

Module Type VC_Correct.


Axiom proof_of_triangle_area_safety_wit_1 : triangle_area_safety_wit_1.
Axiom proof_of_triangle_area_return_wit_1 : triangle_area_return_wit_1.

End VC_Correct.
