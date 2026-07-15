(* xs are coefficients of a polynomial.
find_zero find x such that poly(x) = 0.
find_zero returns only only zero point, even if there are many.
Moreover, find_zero only takes list xs having even number of coefficients
and largest non zero coefficient as it guarantees
a solution.
>>> round(find_zero([1, 2]), 2) # f(x) = 1 + 2x
-0.5
>>> round(find_zero([-6, 11, -6, 1]), 2) # (x - 1) * (x - 2) * (x - 3) = -6 + 11x - 6x^2 + x^3
1.0 *)

(*Spec(input : list float, output : float) :=

​	$∑_{i=0}^{n}$ input[i] * output^i = 0

*)

Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Require Import Coq.Reals.Reals.

(*
 * eval_poly coeffs x 计算多项式 coeffs 在点 x 的值
 *)
Fixpoint eval_poly (coeffs : list R) (x : R) : R :=
  match coeffs with
  | [] => 0%R
  | c :: cs => (c + x * (eval_poly cs x))%R
  end.


(* Pre: input list must be non-empty and have even length (as required by Spec) *)
Definition problem_32_pre (input : list R) : Prop := length input > 0 /\ Nat.Even (length input).

Definition problem_32_spec (input : list R) (output : R) : Prop :=
  (* 后置条件: 0 必须是多项式的一个根。*)
  eval_poly input output = 0%R.

(* QCP 2.0.4 finite-double adapters. *)
Require Import SimpleC.SL.FloatLib.
Definition problem_32_pre_fp64 (coeffs : list fp64) : Prop :=
  Forall fp64_isFinite coeffs /\
  problem_32_pre (map fp64_to_R_total coeffs).
Definition problem_32_eval_fp64
    (coeffs : list fp64) (x out : fp64) : Prop :=
  fp64_isFinite out /\
  fp64_to_R_total out =
    eval_poly (map fp64_to_R_total coeffs) (fp64_to_R_total x).
Definition problem_32_spec_fp64 (coeffs : list fp64) (out : fp64) : Prop :=
  fp64_isFinite out /\
  problem_32_spec (map fp64_to_R_total coeffs) (fp64_to_R_total out).
