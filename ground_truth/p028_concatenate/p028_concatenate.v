(*  Concatenate list of strings into a single string
>>> concatenate([])
''
>>> concatenate(['a', 'b', 'c'])
'abc' *)

(* Spec(input : list string, output : string) :=

​	Concat(input, output) *)

Require Import List String.
Import ListNotations.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.
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

Definition ascii_of_z_28 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_28 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_28 c) (string_of_list_z_28 rest)
  end.

Definition row_payload_z_28 (row : list Z) : list Z :=
  firstn (Z.to_nat (Zlength row - 1)) row.

Definition row_string_z_28 (row : list Z) : string :=
  string_of_list_z_28 (row_payload_z_28 row).

Definition rows_to_strings_z_28 (rows : list (list Z)) : list string :=
  map row_string_z_28 rows.

Definition row_len_z_28 (row : list Z) : Z :=
  string_length (row_payload_z_28 row).

Definition rows_well_formed_28 (rows : list (list Z)) (n : Z) : Prop :=
  Zlength rows = n /\
  forall k,
    0 <= k < n ->
    let row := Znth k rows nil in
    let payload := row_payload_z_28 row in
    row = c_string payload /\
    valid_string payload /\
    all_ascii payload /\
    string_length payload < INT_MAX.

Fixpoint concat_rows_payload_28 (rows : list (list Z)) : list Z :=
  match rows with
  | [] => []
  | row :: rest => row_payload_z_28 row ++ concat_rows_payload_28 rest
  end.

Definition concat_prefix_payload_28 (rows : list (list Z)) (k : Z) : list Z :=
  concat_rows_payload_28 (firstn (Z.to_nat k) rows).

Definition concat_prefix_len_28 (rows : list (list Z)) (k : Z) : Z :=
  Zlength (concat_prefix_payload_28 rows k).

Definition total_prefix_state_28
    (rows : list (list Z)) (k total : Z) : Prop :=
  0 <= k <= Zlength rows /\
  total = 1 + concat_prefix_len_28 rows k.

Definition copy_prefix_state_28
    (rows : list (list Z)) (k pos : Z) (out_l : list Z) : Prop :=
  0 <= k <= Zlength rows /\
  out_l = concat_prefix_payload_28 rows k /\
  pos = Zlength out_l.

Definition problem_28_pre_z (rows : list (list Z)) : Prop :=
  problem_28_pre (rows_to_strings_z_28 rows).

Definition problem_28_spec_z (rows : list (list Z)) (out_l : list Z) : Prop :=
  problem_28_spec (rows_to_strings_z_28 rows) (string_of_list_z_28 out_l).
