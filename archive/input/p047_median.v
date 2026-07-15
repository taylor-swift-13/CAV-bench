(* Return median of elements in the list l.
>>> median([3, 1, 2, 4, 5])
3
>>> median([-10, 4, 6, 1000, 10, 20])
8.0 *)

(* Spec(input : list float, output : float) :=

​	∃Sorted_input,
​		Sorted(input, Sorted_input) /\
​		length(input) % 2 =1  → output = Sorted_input[length(input) / 2] /\
​		length(input) % 2 <>1  → output = (Sorted_input[length(input) / 2] + Sorted_input[length(input) / 2 -1]) /2 *)

Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope R_scope.

(* Pre: input must be non-empty to define median *)
Definition problem_47_pre (input : list R) : Prop := input <> [].

Definition problem_47_spec(input : list R) (output : R) : Prop :=
  exists Sorted_input,
    Sorted Rle Sorted_input /\
    forall r : R, In r input <-> In r Sorted_input /\
    let len := length input in
    let halflen := ((length input) / 2)%nat in
    ((len mod 2 = 1)%nat -> output = nth halflen Sorted_input 0) /\
    ((len mod 2 = 0)%nat -> output = ((nth halflen Sorted_input 0) + (nth (halflen-1) Sorted_input 0)) / 2).

(* QCP 2.0.4 finite-float and in-place-sort adapter. *)
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.SL.FloatLib.
Definition problem_47_pre_fp32 (input : list fp32) : Prop :=
  input <> [] /\ Forall fp32_isFinite input.
Definition problem_47_spec_fp32
    (input sorted : list fp32) (output : fp32) : Prop :=
  let inputR := map fp32_to_R_total input in
  let sortedR := map fp32_to_R_total sorted in
  Permutation inputR sortedR /\
  Sorted Rle sortedR /\
  fp32_isFinite output /\
  let n := length sortedR in
  let half := (n / 2)%nat in
  (((n mod 2 = 1)%nat /\ fp32_to_R_total output = nth half sortedR 0%R) \/
   ((n mod 2 = 0)%nat /\
    fp32_to_R_total output =
      ((nth half sortedR 0%R + nth (half - 1) sortedR 0%R) / 2)%R)).
