(* def total_match(lst1, lst2):
'''
Write a function that accepts two lists of strings and returns the list that has
total number of chars in the all strings of the list less than the other list.

if the two lists have the same number of chars, return the first list.

Examples
total_match([], []) ➞ []
total_match(['hi', 'admin'], ['hI', 'Hi']) ➞ ['hI', 'Hi']
total_match(['hi', 'admin'], ['hi', 'hi', 'admin', 'project']) ➞ ['hi', 'admin']
total_match(['hi', 'admin'], ['hI', 'hi', 'hi']) ➞ ['hI', 'hi', 'hi']
total_match(['4'], ['1', '2', '3', '4', '5']) ➞ ['4']
'''*)
(* 引入必要的库 *)
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.

(* 允许使用列表的标准表示法，例如 [a; b; c] *)
Import ListNotations.
Open Scope string_scope.

(**
 * @spec problem_74_pre
 * @brief 程序前置条件：接受两个字符串列表作为输入。
 *)

Definition problem_74_pre (lst1 lst2 : list string) : Prop := True.

(**
 * @spec problem_74_spec
 * @brief 程序规约：选择两个字符串列表中总字符数较少的那个作为输出（若相等则选择第一个）。
 *)
Definition problem_74_spec (lst1 lst2 output : list string) : Prop :=
  let sum := fun l => fold_left (fun acc s => acc + String.length s) l 0 in
  (sum lst1 <= sum lst2 /\ output = lst1) \/
  (sum lst1 > sum lst2 /\ output = lst2).
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

Definition ascii_of_z_74 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_74 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_74 c) (string_of_list_z_74 rest)
  end.

Definition row_payload_z_74 (row : list Z) : list Z :=
  firstn (Z.to_nat (Zlength row - 1)) row.

Definition row_string_z_74 (row : list Z) : string :=
  string_of_list_z_74 (row_payload_z_74 row).

Definition rows_to_strings_z_74 (rows : list (list Z)) : list string :=
  map row_string_z_74 rows.

Definition row_len_z_74 (row : list Z) : Z :=
  string_length (row_payload_z_74 row).

Fixpoint rows_total_len_z_74 (rows : list (list Z)) : Z :=
  match rows with
  | [] => 0
  | row :: rest => row_len_z_74 row + rows_total_len_z_74 rest
  end.

Definition total_prefix_len_z_74 (rows : list (list Z)) (k : Z) : Z :=
  rows_total_len_z_74 (firstn (Z.to_nat k) rows).

Definition rows_well_formed_74 (rows : list (list Z)) (n : Z) : Prop :=
  Zlength rows = n /\
  0 <= n <= 100 /\
  0 <= rows_total_len_z_74 rows <= INT_MAX /\
  forall k,
    0 <= k < n ->
    let row := Znth k rows nil in
    let payload := row_payload_z_74 row in
    row = c_string payload /\
    valid_string payload /\
    string_length payload < INT_MAX.

Definition total_prefix_state_74
    (rows : list (list Z)) (k total : Z) : Prop :=
  0 <= k <= Zlength rows /\
  total = total_prefix_len_z_74 rows k.

Definition problem_74_pre_z (rows1 rows2 : list (list Z)) : Prop :=
  problem_74_pre (rows_to_strings_z_74 rows1) (rows_to_strings_z_74 rows2).

Definition problem_74_spec_z
    (rows1 rows2 output : list (list Z)) : Prop :=
  problem_74_spec
    (rows_to_strings_z_74 rows1)
    (rows_to_strings_z_74 rows2)
    (rows_to_strings_z_74 output).

Lemma String_length_string_of_list_z_74 : forall l,
  String.length (string_of_list_z_74 l) = List.length l.
Proof.
  induction l as [| x xs IH]; simpl; congruence.
Qed.

Lemma row_string_length_z_74 : forall row,
  Z.of_nat (String.length (row_string_z_74 row)) = row_len_z_74 row.
Proof.
  intros row.
  unfold row_string_z_74, row_len_z_74, string_length.
  rewrite String_length_string_of_list_z_74.
  rewrite Zlength_correct.
  reflexivity.
Qed.

Lemma rows_well_formed_74_row : forall rows n k,
  rows_well_formed_74 rows n ->
  0 <= k < n ->
  let row := Znth k rows nil in
  let payload := row_payload_z_74 row in
  row = c_string payload /\
  valid_string payload /\
  string_length payload < INT_MAX /\
  Zlength row = string_length payload + 1.
Proof.
  intros rows n k [Hlen [_ [_ Hwf]]] Hk row payload.
  specialize (Hwf k Hk).
  destruct Hwf as [Hrow [Hvalid Hlt]].
  split; [exact Hrow|].
  split; [exact Hvalid|].
  split; [exact Hlt|].
  subst row payload.
  change (Zlength (Znth k rows nil) =
          Zlength (row_payload_z_74 (Znth k rows nil)) + 1).
  rewrite Hrow at 1.
  unfold c_string.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma total_prefix_state_74_initial : forall rows,
  total_prefix_state_74 rows 0 0.
Proof.
  intros rows.
  unfold total_prefix_state_74, total_prefix_len_z_74.
  split; [rewrite Zlength_correct; lia|].
  reflexivity.
Qed.

Lemma firstn_succ_Z_74 : forall (rows : list (list Z)) k,
  0 <= k < Zlength rows ->
  firstn (Z.to_nat (k + 1)) rows =
  firstn (Z.to_nat k) rows ++ [Znth k rows nil].
Proof.
  assert (Hnth: forall (rows : list (list Z)) n,
    (n < List.length rows)%nat ->
    firstn (S n) rows = firstn n rows ++ [nth n rows nil]).
  {
    induction rows as [| row rest IH]; intros [| n] Hlt; simpl in *; try lia.
    - reflexivity.
    - rewrite IH by lia.
      reflexivity.
  }
  intros rows k Hk.
  assert (Hsucc: Z.to_nat (k + 1) = S (Z.to_nat k)).
  {
    apply Nat2Z.inj.
    rewrite Z2Nat.id by lia.
    rewrite Nat2Z.inj_succ, Z2Nat.id by lia.
    lia.
  }
  rewrite Hsucc.
  rewrite Hnth.
  - unfold Znth.
    reflexivity.
  - apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct.
    lia.
Qed.

Lemma rows_total_len_z_74_app : forall a b,
  rows_total_len_z_74 (a ++ b) =
  rows_total_len_z_74 a + rows_total_len_z_74 b.
Proof.
  induction a as [| row rest IH]; intros b; simpl.
  - lia.
  - rewrite IH. lia.
Qed.

Lemma total_prefix_state_74_step : forall rows k total len,
  total_prefix_state_74 rows k total ->
  0 <= k < Zlength rows ->
  len = row_len_z_74 (Znth k rows nil) ->
  total_prefix_state_74 rows (k + 1) (total + len).
Proof.
  intros rows k total len [Hkbounds Htotal] Hk Hlen.
  split; [lia|].
  unfold total_prefix_len_z_74 in *.
  rewrite firstn_succ_Z_74 by exact Hk.
  rewrite rows_total_len_z_74_app.
  simpl.
  lia.
Qed.

Lemma total_prefix_state_74_full : forall rows n total,
  Zlength rows = n ->
  total_prefix_state_74 rows n total ->
  total = rows_total_len_z_74 rows.
Proof.
  intros rows n total Hlen [_ Htotal].
  unfold total_prefix_len_z_74 in Htotal.
  subst total.
  rewrite firstn_all2; [reflexivity|].
  rewrite Zlength_correct in Hlen.
  lia.
Qed.

Lemma row_len_z_74_nonneg : forall row,
  0 <= row_len_z_74 row.
Proof.
  intros row.
  unfold row_len_z_74, string_length.
  apply Zlength_nonneg.
Qed.

Lemma rows_total_len_z_74_nonneg : forall rows,
  0 <= rows_total_len_z_74 rows.
Proof.
  induction rows as [| row rest IH]; simpl; [lia|].
  pose proof (row_len_z_74_nonneg row).
  lia.
Qed.

Lemma total_prefix_state_74_bound : forall rows k total,
  total_prefix_state_74 rows k total ->
  total <= rows_total_len_z_74 rows.
Proof.
  intros rows k total [_ Htotal].
  unfold total_prefix_len_z_74 in Htotal.
  subst total.
  rewrite <- (firstn_skipn (Z.to_nat k) rows) at 2.
  rewrite rows_total_len_z_74_app.
  pose proof (rows_total_len_z_74_nonneg (skipn (Z.to_nat k) rows)).
  lia.
Qed.

Lemma total_prefix_state_74_nonneg : forall rows k total,
  total_prefix_state_74 rows k total ->
  0 <= total.
Proof.
  intros rows k total [_ Htotal].
  unfold total_prefix_len_z_74 in Htotal.
  subst total.
  apply rows_total_len_z_74_nonneg.
Qed.

Lemma fold_left_nat_add_start_74 : forall l x,
  fold_left Nat.add l x = (x + fold_left Nat.add l 0)%nat.
Proof.
  induction l as [| a rest IH]; intros x; simpl; [lia|].
  rewrite IH.
  rewrite (IH a).
  lia.
Qed.

Lemma fold_left_string_length_start_74 : forall l x,
  fold_left
    (fun (acc : nat) (s : string) => (acc + String.length s)%nat)
    l x =
  (x +
   fold_left
     (fun (acc : nat) (s : string) => (acc + String.length s)%nat)
     l 0)%nat.
Proof.
  induction l as [| a rest IH]; intros x; simpl; [lia|].
  rewrite IH.
  rewrite (IH (String.length a)).
  lia.
Qed.

Lemma rows_total_len_z_74_nat_sum : forall rows,
  Z.of_nat
    (fold_left
       (fun (acc : nat) (s : string) => (acc + String.length s)%nat)
       (rows_to_strings_z_74 rows) 0%nat) =
  rows_total_len_z_74 rows.
Proof.
  induction rows as [| row rest IH]; simpl.
  - reflexivity.
  - rewrite fold_left_string_length_start_74.
    rewrite Nat2Z.inj_add.
    rewrite IH.
    rewrite row_string_length_z_74.
    lia.
Qed.

Lemma problem_74_spec_z_rows1 : forall rows1 rows2,
  rows_total_len_z_74 rows1 <= rows_total_len_z_74 rows2 ->
  problem_74_spec_z rows1 rows2 rows1.
Proof.
  intros rows1 rows2 Hle.
  unfold problem_74_spec_z, problem_74_spec.
  left.
  split; [| reflexivity].
  apply Nat2Z.inj_le.
  repeat rewrite rows_total_len_z_74_nat_sum.
  exact Hle.
Qed.

Lemma problem_74_spec_z_rows2 : forall rows1 rows2,
  rows_total_len_z_74 rows1 > rows_total_len_z_74 rows2 ->
  problem_74_spec_z rows1 rows2 rows2.
Proof.
  intros rows1 rows2 Hgt.
  unfold problem_74_spec_z, problem_74_spec.
  right.
  split; [| reflexivity].
  apply Nat2Z.inj_lt.
  repeat rewrite rows_total_len_z_74_nat_sum.
  lia.
Qed.
