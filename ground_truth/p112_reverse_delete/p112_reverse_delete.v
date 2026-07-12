(* Task
We are given two strings s and c, you have to deleted all the characters in s that are equal to any character in c
then check if the result string is palindrome.
A string is called palindrome if it reads the same backward as forward.
You should return a tuple containing the result string and True/False for the check.
Example
For s = "abcde", c = "ae", the result should be ('bcd',False)
For s = "abcdef", c = "b" the result should be ('acdef',False)
For s = "abcdedcba", c = "ab", the result should be ('cdedc',True)
*)

Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String Coq.Bool.Bool.
Import ListNotations.



Fixpoint list_eqb {A} (eq : A -> A -> bool) (l1 l2 : list A) : bool :=
  match l1,l2 with
  | [],[] => true
  | x1::t1, x2::t2 => andb (eq x1 x2) (list_eqb eq t1 t2)
  | _,_ => false
  end.

Fixpoint existsb {A} (f : A -> bool) (l : list A) : bool :=
  match l with [] => false | h::t => orb (f h) (existsb f t) end.

Fixpoint delete_chars_impl (s c : list ascii) : list ascii :=
  match s with
  | [] => []
  | h::t => if existsb (fun x => Ascii.eqb x h) c then delete_chars_impl t c else h :: delete_chars_impl t c
  end.

Definition is_pal_impl (s : list ascii) : bool := list_eqb Ascii.eqb s (rev s).

Definition del_and_pal_impl (s c : list ascii) : list ascii * bool :=
  let r := delete_chars_impl s c in (r, is_pal_impl r).

Definition reverse_delete (s c : string) : string * bool :=
  let (r, b) := del_and_pal_impl (list_ascii_of_string s) (list_ascii_of_string c) in
  (string_of_list_ascii r, b).

(* s 与 c 仅包含小写字母 *)
Definition problem_112_pre (s c : string) : Prop :=
  let ls := list_ascii_of_string s in
  let lc := list_ascii_of_string c in
  Forall (fun ch => let n := nat_of_ascii ch in 97 <= n /\ n <= 122) ls /\
  Forall (fun ch => let n := nat_of_ascii ch in 97 <= n /\ n <= 122) lc.

Definition problem_112_spec (s c : string) (output : string * bool) : Prop :=
  output = reverse_delete s c.
Definition spec_existsb_112 {A : Type} := @existsb A.
Definition spec_list_eqb_112 {A : Type} := @list_eqb A.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import SimpleC.StdLib.string_lib.

Import ListNotations.

Local Open Scope Z_scope.


(* Case-local compatibility with the source proof; DLC intentionally keeps the
   benchmark's pinned string library unchanged. *)
Definition strchr_result (str : list Z) (c ret s : Z) : Prop :=
  (exists i,
      0 <= i < string_length str /\
      Znth i str 0 = c /\
      (forall k, 0 <= k < i -> Znth k str 0 <> c) /\
      ret = s + i /\
      ret <> 0) \/
  ((forall k, 0 <= k < string_length str -> Znth k str 0 <> c) /\
   ((c = 0 /\ ret = s + string_length str) \/
    (c <> 0 /\ ret = 0))).
Local Open Scope string_scope.
Local Open Scope list_scope.
Import naive_C_Rules.
Local Open Scope sac.

Definition ascii_of_z_112 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_112 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_112 c) (string_of_list_z_112 rest)
  end.

Definition char_in_z_112 (c : Z) (s : list Z) : Prop :=
  In c s.

Fixpoint char_in_zb_112 (c : Z) (s : list Z) : bool :=
  match s with
  | [] => false
  | x :: xs => if Z.eqb c x then true else char_in_zb_112 c xs
  end.

Fixpoint filter_not_in_z_112 (s c : list Z) : list Z :=
  match s with
  | [] => []
  | x :: xs =>
      if char_in_zb_112 x c
      then filter_not_in_z_112 xs c
      else x :: filter_not_in_z_112 xs c
  end.

Definition filter_prefix_state_112
    (s c : list Z) (i : Z) (out : list Z) : Prop :=
  0 <= i <= Zlength s /\
  out = filter_not_in_z_112 (sublist 0 i s) c.

Definition mirror_prefix_112 (s : list Z) (i : Z) : Prop :=
  forall k,
    0 <= k < i ->
    Znth k s 0 = Znth (Zlength s - 1 - k) s 0.

Definition mirror_mismatch_prefix_112 (s : list Z) (i : Z) : Prop :=
  exists k,
    0 <= k < i /\
    Znth k s 0 <> Znth (Zlength s - 1 - k) s 0.

Definition palindrome_scan_state_112 (s : list Z) (i pal : Z) : Prop :=
  0 <= i <= Zlength s /\
  (pal = 1 -> mirror_prefix_112 s i) /\
  (pal = 0 -> mirror_mismatch_prefix_112 s i) /\
  (pal = 0 \/ pal = 1).

Definition pal_bool_112 (s : list Z) : bool :=
  spec_list_eqb_112 Z.eqb s (rev s).

Definition true_payload_112 : list Z := [84; 114; 117; 101].

Definition false_payload_112 : list Z := [70; 97; 108; 115; 101].

Definition bool_row_112 (b : bool) : list Z :=
  c_string (if b then true_payload_112 else false_payload_112).

Definition reverse_delete_rows_112 (s c : list Z) : list (list Z) :=
  let filtered := filter_not_in_z_112 s c in
  [c_string filtered; bool_row_112 (pal_bool_112 filtered)].

Definition row_payload_z_112 (row : list Z) : list Z :=
  firstn (Z.to_nat (Zlength row - 1)) row.

Definition row_string_z_112 (row : list Z) : string :=
  string_of_list_z_112 (row_payload_z_112 row).

Definition rows_to_output_112 (rows : list (list Z)) : string * bool :=
  match rows with
  | r :: b :: _ =>
      (row_string_z_112 r,
       if spec_list_eqb_112 Z.eqb (row_payload_z_112 b) true_payload_112
       then true
       else false)
  | _ => (EmptyString, false)
  end.

Definition problem_112_pre_z (s c : list Z) : Prop :=
  problem_112_pre (string_of_list_z_112 s) (string_of_list_z_112 c).

Definition problem_112_spec_z (s c : list Z) (rows : list (list Z)) : Prop :=
  problem_112_spec
    (string_of_list_z_112 s)
    (string_of_list_z_112 c)
    (rows_to_output_112 rows).

Definition valid_lower_payload_112 (s : list Z) : Prop :=
  forall i, 0 <= i < Zlength s -> 97 <= Znth i s 0 <= 122.

Definition valid_reverse_delete_input_112 (s c : list Z) : Prop :=
  valid_lower_payload_112 s /\ valid_lower_payload_112 c.
