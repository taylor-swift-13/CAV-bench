(* """ Return list of all prefixes from shortest to longest of the input string
>>> all_prefixes('abc')
['a', 'ab', 'abc']
""" *)

(* Spec(input, output) :=

(length(input) = 0 ∧ output = {}) ∨
(length(input) > 0 ∧
  length(output) = length(input) ∧
  ∀ i ∈ [0, length(input)),
    length(output[i]) = i+1 ∧
    prefix(output[i], input)
) *)

Require Import List Ascii String.
Import ListNotations.
Open Scope string_scope.

(* Pre: no additional constraints for `all_prefixes` by default *)
Definition problem_14_pre (input : string) : Prop := True.

Definition problem_14_spec (input : string)(output : list string) : Prop :=
  (String.length input = 0 /\ output = []) \/
  (String.length input > 0 /\
   List.length output = String.length input /\
   forall i, i < String.length input ->
     String.length (nth i output "0") = i + 1 /\
     prefix (nth i output "0") input = true).
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import SimpleC.StdLib.string_lib.

Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Import naive_C_Rules.
Local Open Scope sac.

Definition ascii_of_z_14 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_14 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_14 c) (string_of_list_z_14 rest)
  end.

Definition row_payload_z_14 (row : list Z) : list Z :=
  firstn (Z.to_nat (Zlength row - 1)) row.

Definition row_string_z_14 (row : list Z) : string :=
  string_of_list_z_14 (row_payload_z_14 row).

Definition rows_to_strings_z_14 (rows : list (list Z)) : list string :=
  map row_string_z_14 rows.

Definition prefix_row_payload_14 (s : list Z) (i : Z) : list Z :=
  sublist 0 (i + 1) s.

Definition prefix_row_14 (s : list Z) (i : Z) : list Z :=
  c_string (prefix_row_payload_14 s i).

Fixpoint prefix_payloads_nat_14 (s : list Z) (n : nat) : list (list Z) :=
  match n with
  | O => []
  | S k => prefix_payloads_nat_14 s k ++ [firstn (S k) s]
  end.

Definition prefix_rows_14 (s : list Z) (n : Z) : list (list Z) :=
  map c_string (prefix_payloads_nat_14 s (Z.to_nat n)).

Definition prefix_rows_state_14
    (s : list Z) (n : Z) (rows : list (list Z)) : Prop :=
  0 <= n <= string_length s /\ rows = prefix_rows_14 s n.

Definition prefix_row_block_14 (pr : Z * list Z) : Assertion :=
  CharArray.full (fst pr) (Zlength (snd pr)) (snd pr).

Fixpoint prefix_rows_heap_14
    (row_ptrs : list Z) (rows : list (list Z)) : Assertion :=
  match row_ptrs, rows with
  | p :: ps, row :: rs =>
      CharArray.full p (Zlength row) row ** prefix_rows_heap_14 ps rs
  | _, _ => emp
  end.

Definition valid_prefixes_14 (s : list Z) : Prop :=
  string_length s + 2 < INT_MAX.

Definition problem_14_pre_z (s : list Z) : Prop :=
  problem_14_pre (string_of_list_z_14 s).

Definition problem_14_spec_z (s : list Z) (rows : list (list Z)) : Prop :=
  problem_14_spec (string_of_list_z_14 s) (rows_to_strings_z_14 rows).
