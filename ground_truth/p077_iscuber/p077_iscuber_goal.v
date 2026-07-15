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
Require Import p077_iscuber.
Local Open Scope sac.

(*----- Function abs -----*)

Definition abs_safety_wit_1 := 
forall (x_pre: Z) (PreH1 : (INT_MIN < x_pre)) (PreH2 : (x_pre <= INT_MAX)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition abs_safety_wit_2 := 
forall (x_pre: Z) (PreH1 : (x_pre < 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (x_pre <> (INT_MIN)) ”
.

Definition abs_return_wit_1 := 
(
forall (x_pre: Z) (PreH1 : (x_pre >= 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (x_pre = (Zabs (x_pre))) ”
  &&  emp
) \/
(
forall (x_pre: Z) (PreH1 : (x_pre >= 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (x_pre = (Zabs (x_pre))) ”
  &&  emp
).

Definition abs_return_wit_1_split_goal_1 := 
forall (x_pre: Z) (PreH1 : (x_pre >= 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  (x_pre = (Zabs (x_pre)))
.

Definition abs_return_wit_2 := 
(
forall (x_pre: Z) (PreH1 : (x_pre < 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((-x_pre) = (Zabs (x_pre))) ”
  &&  emp
) \/
(
forall (x_pre: Z) (PreH1 : (x_pre < 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((-x_pre) = (Zabs (x_pre))) ”
  &&  emp
).

Definition abs_return_wit_2_split_goal_1 := 
forall (x_pre: Z) (PreH1 : (x_pre < 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  ((-x_pre) = (Zabs (x_pre)))
.

(*----- Function iscuber -----*)

Definition iscuber_safety_wit_1 := 
forall (a_pre: Z) (PreH1 : ((-2146689000) <= a_pre)) (PreH2 : (a_pre <= 2146689000)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition iscuber_safety_wit_2 := 
forall (a_pre: Z) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= 1290)) (PreH3 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> (((k * k ) * k ) <> (Zabs (a_pre))))) (PreH4 : ((-2146689000) <= a_pre)) (PreH5 : (a_pre <= 2146689000)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (((i * i ) * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i * i ) * i )) ”
.

Definition iscuber_safety_wit_3 := 
forall (a_pre: Z) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= 1290)) (PreH3 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> (((k * k ) * k ) <> (Zabs (a_pre))))) (PreH4 : ((-2146689000) <= a_pre)) (PreH5 : (a_pre <= 2146689000)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((i * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * i )) ”
.

Definition iscuber_safety_wit_4 := 
forall (a_pre: Z) (i: Z) (retval: Z) (PreH1 : (((i * i ) * i ) <= retval)) (PreH2 : (retval = (Zabs (a_pre)))) (PreH3 : (0 <= i)) (PreH4 : (i <= 1290)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> (((k * k ) * k ) <> (Zabs (a_pre))))) (PreH6 : ((-2146689000) <= a_pre)) (PreH7 : (a_pre <= 2146689000)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (((i * i ) * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i * i ) * i )) ”
.

Definition iscuber_safety_wit_5 := 
forall (a_pre: Z) (i: Z) (retval: Z) (PreH1 : (((i * i ) * i ) <= retval)) (PreH2 : (retval = (Zabs (a_pre)))) (PreH3 : (0 <= i)) (PreH4 : (i <= 1290)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> (((k * k ) * k ) <> (Zabs (a_pre))))) (PreH6 : ((-2146689000) <= a_pre)) (PreH7 : (a_pre <= 2146689000)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((i * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * i )) ”
.

Definition iscuber_safety_wit_6 := 
forall (a_pre: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (((i * i ) * i ) = retval_2)) (PreH2 : (retval_2 = (Zabs (a_pre)))) (PreH3 : (((i * i ) * i ) <= retval)) (PreH4 : (retval = (Zabs (a_pre)))) (PreH5 : (0 <= i)) (PreH6 : (i <= 1290)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> (((k * k ) * k ) <> (Zabs (a_pre))))) (PreH8 : ((-2146689000) <= a_pre)) (PreH9 : (a_pre <= 2146689000)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition iscuber_safety_wit_7 := 
forall (a_pre: Z) (i: Z) (retval: Z) (PreH1 : (((i * i ) * i ) > retval)) (PreH2 : (retval = (Zabs (a_pre)))) (PreH3 : (0 <= i)) (PreH4 : (i <= 1290)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> (((k * k ) * k ) <> (Zabs (a_pre))))) (PreH6 : ((-2146689000) <= a_pre)) (PreH7 : (a_pre <= 2146689000)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition iscuber_safety_wit_8 := 
forall (a_pre: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (((i * i ) * i ) <> retval_2)) (PreH2 : (retval_2 = (Zabs (a_pre)))) (PreH3 : (((i * i ) * i ) <= retval)) (PreH4 : (retval = (Zabs (a_pre)))) (PreH5 : (0 <= i)) (PreH6 : (i <= 1290)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> (((k * k ) * k ) <> (Zabs (a_pre))))) (PreH8 : ((-2146689000) <= a_pre)) (PreH9 : (a_pre <= 2146689000)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition iscuber_entail_wit_1 := 
forall (a_pre: Z) (PreH1 : ((-2146689000) <= a_pre)) (PreH2 : (a_pre <= 2146689000)) ,
  TT && emp 
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1290) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 0)) -> (((k * k ) * k ) <> (Zabs (a_pre)))) ” 
  &&  “ ((-2146689000) <= a_pre) ” 
  &&  “ (a_pre <= 2146689000) ”
  &&  emp
.

Definition iscuber_entail_wit_2 := 
(
forall (a_pre: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (((i * i ) * i ) <> retval_2)) (PreH2 : (retval_2 = (Zabs (a_pre)))) (PreH3 : (((i * i ) * i ) <= retval)) (PreH4 : (retval = (Zabs (a_pre)))) (PreH5 : (0 <= i)) (PreH6 : (i <= 1290)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> (((k * k ) * k ) <> (Zabs (a_pre))))) (PreH8 : ((-2146689000) <= a_pre)) (PreH9 : (a_pre <= 2146689000)) ,
  TT && emp 
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 1290) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> (((k * k ) * k ) <> (Zabs (a_pre)))) ” 
  &&  “ ((-2146689000) <= a_pre) ” 
  &&  “ (a_pre <= 2146689000) ”
  &&  emp
) \/
(
forall (a_pre: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (((i * i ) * i ) <> retval_2)) (PreH2 : (retval_2 = (Zabs (a_pre)))) (PreH3 : (((i * i ) * i ) <= retval)) (PreH4 : (retval = (Zabs (a_pre)))) (PreH5 : (0 <= i)) (PreH6 : (i <= 1290)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> (((k * k ) * k ) <> (Zabs (a_pre))))) (PreH8 : ((-2146689000) <= a_pre)) (PreH9 : (a_pre <= 2146689000)) ,
  TT && emp 
|--
  “ ((((0 * 0 ) * 0 ) <> (Zabs (a_pre))) /\ (((((i + 1 ) - 1 ) * ((i + 1 ) - 1 ) ) * ((i + 1 ) - 1 ) ) <> (Zabs (a_pre)))) ” 
  &&  “ ((i + 1 ) <= 1290) ”
  &&  emp
).

Definition iscuber_entail_wit_2_split_goal_1 := 
forall (a_pre: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (((i * i ) * i ) <> retval_2)) (PreH2 : (retval_2 = (Zabs (a_pre)))) (PreH3 : (((i * i ) * i ) <= retval)) (PreH4 : (retval = (Zabs (a_pre)))) (PreH5 : (0 <= i)) (PreH6 : (i <= 1290)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> (((k * k ) * k ) <> (Zabs (a_pre))))) (PreH8 : ((-2146689000) <= a_pre)) (PreH9 : (a_pre <= 2146689000)) ,
  ((((0 * 0 ) * 0 ) <> (Zabs (a_pre))) /\ (((((i + 1 ) - 1 ) * ((i + 1 ) - 1 ) ) * ((i + 1 ) - 1 ) ) <> (Zabs (a_pre))))
.

Definition iscuber_entail_wit_2_split_goal_2 := 
forall (a_pre: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (((i * i ) * i ) <> retval_2)) (PreH2 : (retval_2 = (Zabs (a_pre)))) (PreH3 : (((i * i ) * i ) <= retval)) (PreH4 : (retval = (Zabs (a_pre)))) (PreH5 : (0 <= i)) (PreH6 : (i <= 1290)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> (((k * k ) * k ) <> (Zabs (a_pre))))) (PreH8 : ((-2146689000) <= a_pre)) (PreH9 : (a_pre <= 2146689000)) ,
  ((i + 1 ) <= 1290)
.

Definition iscuber_return_wit_1 := 
(
forall (a_pre: Z) (i: Z) (retval: Z) (PreH1 : (((i * i ) * i ) > retval)) (PreH2 : (retval = (Zabs (a_pre)))) (PreH3 : (0 <= i)) (PreH4 : (i <= 1290)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> (((k * k ) * k ) <> (Zabs (a_pre))))) (PreH6 : ((-2146689000) <= a_pre)) (PreH7 : (a_pre <= 2146689000)) ,
  TT && emp 
|--
  “ (problem_77_spec_z a_pre 0 ) ”
  &&  emp
) \/
(
forall (a_pre: Z) (i: Z) (retval: Z) (PreH1 : (((i * i ) * i ) > retval)) (PreH2 : (retval = (Zabs (a_pre)))) (PreH3 : (0 <= i)) (PreH4 : (i <= 1290)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> (((k * k ) * k ) <> (Zabs (a_pre))))) (PreH6 : ((-2146689000) <= a_pre)) (PreH7 : (a_pre <= 2146689000)) ,
  TT && emp 
|--
  “ (problem_77_spec_z a_pre 0 ) ”
  &&  emp
).

Definition iscuber_return_wit_1_split_goal_1 := 
forall (a_pre: Z) (i: Z) (retval: Z) (PreH1 : (((i * i ) * i ) > retval)) (PreH2 : (retval = (Zabs (a_pre)))) (PreH3 : (0 <= i)) (PreH4 : (i <= 1290)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> (((k * k ) * k ) <> (Zabs (a_pre))))) (PreH6 : ((-2146689000) <= a_pre)) (PreH7 : (a_pre <= 2146689000)) ,
  (problem_77_spec_z a_pre 0 )
.

Definition iscuber_return_wit_2 := 
(
forall (a_pre: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (((i * i ) * i ) = retval_2)) (PreH2 : (retval_2 = (Zabs (a_pre)))) (PreH3 : (((i * i ) * i ) <= retval)) (PreH4 : (retval = (Zabs (a_pre)))) (PreH5 : (0 <= i)) (PreH6 : (i <= 1290)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> (((k * k ) * k ) <> (Zabs (a_pre))))) (PreH8 : ((-2146689000) <= a_pre)) (PreH9 : (a_pre <= 2146689000)) ,
  TT && emp 
|--
  “ (problem_77_spec_z a_pre 1 ) ”
  &&  emp
) \/
(
forall (a_pre: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (((i * i ) * i ) = retval_2)) (PreH2 : (retval_2 = (Zabs (a_pre)))) (PreH3 : (((i * i ) * i ) <= retval)) (PreH4 : (retval = (Zabs (a_pre)))) (PreH5 : (0 <= i)) (PreH6 : (i <= 1290)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> (((k * k ) * k ) <> (Zabs (a_pre))))) (PreH8 : ((-2146689000) <= a_pre)) (PreH9 : (a_pre <= 2146689000)) ,
  TT && emp 
|--
  “ (problem_77_spec_z a_pre 1 ) ”
  &&  emp
).

Definition iscuber_return_wit_2_split_goal_1 := 
forall (a_pre: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (((i * i ) * i ) = retval_2)) (PreH2 : (retval_2 = (Zabs (a_pre)))) (PreH3 : (((i * i ) * i ) <= retval)) (PreH4 : (retval = (Zabs (a_pre)))) (PreH5 : (0 <= i)) (PreH6 : (i <= 1290)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> (((k * k ) * k ) <> (Zabs (a_pre))))) (PreH8 : ((-2146689000) <= a_pre)) (PreH9 : (a_pre <= 2146689000)) ,
  (problem_77_spec_z a_pre 1 )
.

Definition iscuber_partial_solve_wit_1_pure := 
forall (a_pre: Z) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= 1290)) (PreH3 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> (((k * k ) * k ) <> (Zabs (a_pre))))) (PreH4 : ((-2146689000) <= a_pre)) (PreH5 : (a_pre <= 2146689000)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (INT_MIN < a_pre) ” 
  &&  “ (a_pre <= INT_MAX) ”
.

Definition iscuber_partial_solve_wit_1_aux := 
forall (a_pre: Z) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= 1290)) (PreH3 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> (((k * k ) * k ) <> (Zabs (a_pre))))) (PreH4 : ((-2146689000) <= a_pre)) (PreH5 : (a_pre <= 2146689000)) ,
  TT && emp 
|--
  “ (INT_MIN < a_pre) ” 
  &&  “ (a_pre <= INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 1290) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> (((k * k ) * k ) <> (Zabs (a_pre)))) ” 
  &&  “ ((-2146689000) <= a_pre) ” 
  &&  “ (a_pre <= 2146689000) ”
  &&  emp
.

Definition iscuber_partial_solve_wit_1 := iscuber_partial_solve_wit_1_pure -> iscuber_partial_solve_wit_1_aux.

Definition iscuber_partial_solve_wit_2_pure := 
forall (a_pre: Z) (i: Z) (retval: Z) (PreH1 : (((i * i ) * i ) <= retval)) (PreH2 : (retval = (Zabs (a_pre)))) (PreH3 : (0 <= i)) (PreH4 : (i <= 1290)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> (((k * k ) * k ) <> (Zabs (a_pre))))) (PreH6 : ((-2146689000) <= a_pre)) (PreH7 : (a_pre <= 2146689000)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (INT_MIN < a_pre) ” 
  &&  “ (a_pre <= INT_MAX) ”
.

Definition iscuber_partial_solve_wit_2_aux := 
forall (a_pre: Z) (i: Z) (retval: Z) (PreH1 : (((i * i ) * i ) <= retval)) (PreH2 : (retval = (Zabs (a_pre)))) (PreH3 : (0 <= i)) (PreH4 : (i <= 1290)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> (((k * k ) * k ) <> (Zabs (a_pre))))) (PreH6 : ((-2146689000) <= a_pre)) (PreH7 : (a_pre <= 2146689000)) ,
  TT && emp 
|--
  “ (INT_MIN < a_pre) ” 
  &&  “ (a_pre <= INT_MAX) ” 
  &&  “ (((i * i ) * i ) <= retval) ” 
  &&  “ (retval = (Zabs (a_pre))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 1290) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> (((k * k ) * k ) <> (Zabs (a_pre)))) ” 
  &&  “ ((-2146689000) <= a_pre) ” 
  &&  “ (a_pre <= 2146689000) ”
  &&  emp
.

Definition iscuber_partial_solve_wit_2 := iscuber_partial_solve_wit_2_pure -> iscuber_partial_solve_wit_2_aux.

Module Type VC_Correct.


Axiom proof_of_abs_safety_wit_1 : abs_safety_wit_1.
Axiom proof_of_abs_safety_wit_2 : abs_safety_wit_2.
Axiom proof_of_abs_return_wit_1 : abs_return_wit_1.
Axiom proof_of_abs_return_wit_2 : abs_return_wit_2.
Axiom proof_of_iscuber_safety_wit_1 : iscuber_safety_wit_1.
Axiom proof_of_iscuber_safety_wit_2 : iscuber_safety_wit_2.
Axiom proof_of_iscuber_safety_wit_3 : iscuber_safety_wit_3.
Axiom proof_of_iscuber_safety_wit_4 : iscuber_safety_wit_4.
Axiom proof_of_iscuber_safety_wit_5 : iscuber_safety_wit_5.
Axiom proof_of_iscuber_safety_wit_6 : iscuber_safety_wit_6.
Axiom proof_of_iscuber_safety_wit_7 : iscuber_safety_wit_7.
Axiom proof_of_iscuber_safety_wit_8 : iscuber_safety_wit_8.
Axiom proof_of_iscuber_entail_wit_1 : iscuber_entail_wit_1.
Axiom proof_of_iscuber_entail_wit_2 : iscuber_entail_wit_2.
Axiom proof_of_iscuber_return_wit_1 : iscuber_return_wit_1.
Axiom proof_of_iscuber_return_wit_2 : iscuber_return_wit_2.
Axiom proof_of_iscuber_partial_solve_wit_1_pure : iscuber_partial_solve_wit_1_pure.
Axiom proof_of_iscuber_partial_solve_wit_1 : iscuber_partial_solve_wit_1.
Axiom proof_of_iscuber_partial_solve_wit_2_pure : iscuber_partial_solve_wit_2_pure.
Axiom proof_of_iscuber_partial_solve_wit_2 : iscuber_partial_solve_wit_2.

End VC_Correct.
