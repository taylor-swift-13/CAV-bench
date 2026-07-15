(* For a given list of input numbers, calculate Mean Absolute Deviation
around the mean of this dataset.
Mean Absolute Deviation is the average absolute difference between each
element and a centerpoint (mean in this case):
MAD = average | x - x_mean |
>>> mean_absolute_deviation([1.0, 2.0, 3.0, 4.0])
1.0 *)

Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lra.
Require Import Coq.Init.Nat.
Require Import SimpleC.SL.FloatLib.
Import ListNotations.

Open Scope R_scope.

Definition problem_4_pre (l : list R) : Prop := l <> [].

Definition problem_4_spec (l : list R) (mad : R) : Prop :=
  let n := length l in
  let mu := fold_right Rplus 0 l / INR n in
  mad = fold_right (fun x acc => acc + Rabs (x - mu)) 0 l / INR n.

Definition problem_4_pre_fp32 (l : list fp32) : Prop :=
  Forall fp32_isFinite l /\ problem_4_pre (map fp32_to_R_total l).

Definition problem_4_spec_fp32 (l : list fp32) (mad : fp32) : Prop :=
  fp32_isFinite mad /\
  problem_4_spec (map fp32_to_R_total l) (fp32_to_R_total mad).
