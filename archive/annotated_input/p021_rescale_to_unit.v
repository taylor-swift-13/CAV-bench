(* """ Given list of numbers (of at least two elements), apply a linear transform to that list,
such that the smallest number will become 0 and the largest will become 1
>>> rescale_to_unit([1.0, 2.0, 3.0, 4.0, 5.0])
[0.0, 0.25, 0.5, 0.75, 1.0]
""" *)
(*Spec(input : list float, output : list float) :=

​	length(input) = length(output) ∧
  ∀ i ∈ [0, length(input)), output[i] = (input[i] - min(input)) / (max(input) - min(input))  /\
 *)


Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.RIneq.

Import ListNotations.

Open Scope R_scope.

(* 谓词 is_list_min 和 is_list_max  *)
Definition is_list_min (l : list R) (m : R) : Prop :=
  In m l /\ (forall x, In x l -> m <= x).

Definition is_list_max (l : list R) (m : R) : Prop :=
  In m l /\ (forall x, In x l -> m >= x).


(* Pre: no additional constraints for `rescale_to_unit` by default *)
Definition problem_21_pre (input : list R) : Prop := (length input >= 2)%nat.

Definition problem_21_spec (input output : list R) : Prop :=
  exists min_val max_val,
    is_list_min input min_val /\
    is_list_max input max_val /\
    (output = map (fun x => (x - min_val) / (max_val - min_val)) input).

(* QCP 2.0.4 finite-float adapter, including the constant-input case. *)
Require Import SimpleC.SL.FloatLib.
Definition problem_21_pre_fp32 (input : list fp32) : Prop :=
  Forall fp32_isFinite input /\
  problem_21_pre (map fp32_to_R_total input).
Definition problem_21_spec_fp32 (input output : list fp32) : Prop :=
  let xs := map fp32_to_R_total input in
  let ys := map fp32_to_R_total output in
  Forall fp32_isFinite output /\
  exists min_val max_val,
    is_list_min xs min_val /\
    is_list_max xs max_val /\
    ((max_val = min_val /\ ys = repeat 0%R (length xs)) \/
     (max_val <> min_val /\
      ys = map (fun x => (x - min_val) / (max_val - min_val)) xs)).
