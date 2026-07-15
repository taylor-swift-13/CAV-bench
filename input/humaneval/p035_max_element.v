(* Return maximum element in the list.
>>> max_element([1, 2, 3])
3
>>> max_element([5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10])
123 *)

(* Spec(input : list int, output : int) :=
	output = max(input) *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

(* Pre: input must be non-empty *)
Definition problem_35_pre (input : list Z) : Prop := input <> []%list.

Definition problem_35_spec (input : list Z) (output : Z) : Prop :=
  In output input /\
  forall x, In x input -> (x <= output)%Z.

Definition problem_35_prefix (input : list Z) (i current : Z) : Prop :=
  In current (firstn (Z.to_nat i) input) /\
  forall x, In x (firstn (Z.to_nat i) input) -> (x <= current)%Z.
