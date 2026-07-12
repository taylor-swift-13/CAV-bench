(* def sorted_list_sum(lst):
"""Write a function that accepts a list of strings as a parameter,
deletes the strings that have odd lengths from it,
and returns the resulted list with a sorted order,
The list is always a list of strings and never an array of numbers,
and it may contain duplicates.
The order of the list should be ascending by length of each word, and you
should return the list sorted by that rule.
If two words have the same length, sort the list alphabetically.
The function should return a list of strings in sorted order.
You may assume that all words will have the same length.
For example:
assert list_sort(["aa", "a", "aaa"]) => ["aa"]
assert list_sort(["ab", "a", "aaa", "cd"]) => ["ab", "cd"]
""" *)

Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String Coq.Arith.PeanoNat.
Require Import Coq.Sorting.Permutation Coq.Sorting.Sorted Coq.Structures.OrderedTypeEx.
Import ListNotations.


Definition lex_le (s1 s2 : string) : Prop :=
  String_as_OT.lt s1 s2 \/ s1 = s2.

Definition string_le (s1 s2 : string) : Prop :=
  String.length s1 < String.length s2 \/
  String.length s1 = String.length s2 /\ lex_le s1 s2.

Definition has_even_length (s : string) : bool := Nat.even (length s).

(* 任意字符串列表输入均可 *)
Definition problem_149_pre (input : list string) : Prop := True.

Definition problem_149_spec (input : list string) (output : list string) : Prop :=
  Permutation output (filter has_even_length input) /\
  StronglySorted string_le output.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import SimpleC.StdLib.string_lib.

Import ListNotations.
Import naive_C_Rules.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope sac.

Definition ascii_of_z_149 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_149 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_149 c) (string_of_list_z_149 rest)
  end.

Definition row_payload_z_149 (row : list Z) : list Z :=
  firstn (Z.to_nat (Zlength row - 1)) row.

Definition row_string_z_149 (row : list Z) : string :=
  string_of_list_z_149 (row_payload_z_149 row).

Definition rows_to_strings_z_149 (rows : list (list Z)) : list string :=
  map row_string_z_149 rows.

Definition rows_length (rows : list (list Z)) : Z :=
  Zlength rows.

Definition ptrs_length (ptrs : list Z) : Z :=
  Zlength ptrs.

Definition rows_length_149 := rows_length.

Definition ptrs_length_149 := ptrs_length.

Definition row_len_z_149 (row : list Z) : Z :=
  string_lib.string_length (row_payload_z_149 row).

Definition even_row_z_149 (row : list Z) : bool :=
  Z.even (row_len_z_149 row).

Fixpoint filter_even_rows_149 (rows : list (list Z)) : list (list Z) :=
  match rows with
  | [] => []
  | row :: rest =>
      if even_row_z_149 row
      then row :: filter_even_rows_149 rest
      else filter_even_rows_149 rest
  end.

Definition filter_even_prefix_149 (rows : list (list Z)) (k : Z) : list (list Z) :=
  filter_even_rows_149 (firstn (Z.to_nat k) rows).

Definition filter_even_state_149
    (rows : list (list Z)) (k : Z) (output_rows : list (list Z)) : Prop :=
  0 <= k <= Zlength rows /\
  output_rows = filter_even_prefix_149 rows k.

Definition string_rows_sorted (rows : list (list Z)) : Prop :=
  StronglySorted string_le (rows_to_strings_z_149 rows).

Definition string_rows_sorted_149 := string_rows_sorted.

Definition Permutation_rows_149 (a b : list (list Z)) : Prop :=
  Permutation a b.

Definition problem_149_pre_z (rows : list (list Z)) : Prop :=
  problem_149_pre (rows_to_strings_z_149 rows).

Definition problem_149_spec_z
    (rows : list (list Z)) (output_rows : list (list Z)) : Prop :=
  problem_149_spec (rows_to_strings_z_149 rows) (rows_to_strings_z_149 output_rows).

Definition rows_well_formed_149 (rows : list (list Z)) (n : Z) : Prop :=
  Zlength rows = n /\
  n < INT_MAX /\
  forall k,
    0 <= k < n ->
    let row := Znth k rows nil in
    let payload := row_payload_z_149 row in
    row = string_lib.c_string payload /\
    string_lib.valid_string payload /\
    string_lib.string_length payload < INT_MAX.

Definition filter_even_step_keep_149
    (rows : list (list Z)) (i : Z) (output_rows : list (list Z)) : Prop :=
  filter_even_state_149 rows (i + 1) output_rows.

Definition filter_even_step_take_149
    (rows : list (list Z)) (i : Z)
    (output_rows output_rows_next : list (list Z)) : Prop :=
  output_rows_next = output_rows ++ [Znth i rows nil] /\
  filter_even_state_149 rows (i + 1) output_rows_next.

Definition problem_149_spec_z_of_sorted_filter
    (rows filtered sorted : list (list Z)) : Prop :=
  filter_even_state_149 rows (Zlength rows) filtered ->
  Permutation_rows_149 filtered sorted ->
  string_rows_sorted_149 sorted ->
  problem_149_spec_z rows sorted.

Definition problem_149_spec_z_of_sorted_prefix
    (rows sorted : list (list Z)) : Prop :=
  Permutation_rows_149 (filter_even_prefix_149 rows (Zlength rows)) sorted ->
  string_rows_sorted_149 sorted ->
  problem_149_spec_z rows sorted.

Lemma string_length_string_of_list_z_149 : forall l,
  String.length (string_of_list_z_149 l) = List.length l.
Proof.
  induction l as [|x xs IH]; simpl; congruence.
Qed.

Lemma row_string_length_z_149 : forall row,
  Z.of_nat (String.length (row_string_z_149 row)) = row_len_z_149 row.
Proof.
  intros row.
  unfold row_string_z_149, row_len_z_149, string_lib.string_length.
  rewrite string_length_string_of_list_z_149.
  rewrite Zlength_correct.
  reflexivity.
Qed.

Lemma Z_even_odd_of_nat_149 : forall n,
  Z.even (Z.of_nat n) = Nat.even n /\
  Z.odd (Z.of_nat n) = Nat.odd n.
Proof.
  induction n as [|n [IHeven IHodd]].
  - split; reflexivity.
  - rewrite Nat2Z.inj_succ.
    split.
    + rewrite Z.even_succ, Nat.even_succ.
      exact IHodd.
    + rewrite Z.odd_succ, Nat.odd_succ.
      exact IHeven.
Qed.

Lemma Z_even_of_nat_149 : forall n,
  Z.even (Z.of_nat n) = Nat.even n.
Proof.
  intro n.
  apply Z_even_odd_of_nat_149.
Qed.

Lemma even_row_has_even_length_149 : forall row,
  even_row_z_149 row = has_even_length (row_string_z_149 row).
Proof.
  intros row.
  unfold even_row_z_149, has_even_length.
  rewrite <- row_string_length_z_149.
  apply Z_even_of_nat_149.
Qed.

Lemma rows_well_formed_149_row : forall rows n k,
  rows_well_formed_149 rows n ->
  0 <= k < n ->
  let row := Znth k rows nil in
  let payload := row_payload_z_149 row in
    row = string_lib.c_string payload /\
    string_lib.valid_string payload /\
    string_lib.string_length payload < INT_MAX.
Proof.
  intros rows n k [_ [_ Hrows]] Hk.
  specialize (Hrows k Hk).
  tauto.
Qed.

Lemma c_string_Zlength_149 : forall payload,
  Zlength (string_lib.c_string payload) = string_lib.string_length payload + 1.
Proof.
  intros payload.
  unfold string_lib.c_string, string_lib.string_length.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma row_payload_c_string_149 : forall rows n k,
  rows_well_formed_149 rows n ->
  0 <= k < n ->
  string_lib.c_string (row_payload_z_149 (Znth k rows nil)) =
  Znth k rows nil.
Proof.
  intros rows n k Hwf Hk.
  pose proof (rows_well_formed_149_row rows n k Hwf Hk) as Hrow.
  simpl in Hrow.
  destruct Hrow as [Hrow _].
  symmetry.
  exact Hrow.
Qed.

Lemma row_payload_c_string_payload_149 : forall payload,
  row_payload_z_149 (string_lib.c_string payload) = payload.
Proof.
  intros payload.
  unfold row_payload_z_149, string_lib.c_string.
  replace (Z.to_nat (Zlength (payload ++ [0]) - 1)) with (List.length payload).
  - change (firstn (List.length payload) (payload ++ [0]) = payload).
    rewrite firstn_app.
    rewrite firstn_all.
    rewrite Nat.sub_diag.
    simpl.
    rewrite app_nil_r.
    reflexivity.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil, Zlength_correct.
    replace (Z.of_nat (List.length payload) + Z.succ 0 - 1)
      with (Z.of_nat (List.length payload)) by lia.
    symmetry.
    apply Nat2Z.id.
Qed.

Lemma filter_even_rows_149_app_take : forall rows row,
  even_row_z_149 row = true ->
  filter_even_rows_149 (rows ++ [row]) =
  filter_even_rows_149 rows ++ [row].
Proof.
  induction rows as [|h t IH]; intros row Heven; simpl.
  - rewrite Heven. reflexivity.
  - destruct (even_row_z_149 h); simpl; rewrite IH by exact Heven; reflexivity.
Qed.

Lemma filter_even_rows_149_app_keep : forall rows row,
  even_row_z_149 row = false ->
  filter_even_rows_149 (rows ++ [row]) =
  filter_even_rows_149 rows.
Proof.
  induction rows as [|h t IH]; intros row Heven; simpl.
  - rewrite Heven. reflexivity.
  - destruct (even_row_z_149 h); simpl; rewrite IH by exact Heven; reflexivity.
Qed.

Lemma filter_even_prefix_149_snoc : forall (rows : list (list Z)) i,
  0 <= i < Zlength rows ->
  firstn (Z.to_nat (i + 1)) rows =
  firstn (Z.to_nat i) rows ++ [Znth i rows (@nil Z)].
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
  intros rows i Hi.
  assert (Hsucc: Z.to_nat (i + 1) = S (Z.to_nat i)).
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

Lemma filter_even_step_take_149_valid : forall rows i output_rows,
  0 <= i < Zlength rows ->
  filter_even_state_149 rows i output_rows ->
  even_row_z_149 (Znth i rows nil) = true ->
  filter_even_state_149 rows (i + 1)
    (output_rows ++ [Znth i rows nil]).
Proof.
  intros rows i output_rows Hi [Hrange Hstate] Heven.
  split; [lia|].
  unfold filter_even_prefix_149 in *.
  rewrite filter_even_prefix_149_snoc by lia.
  rewrite filter_even_rows_149_app_take by exact Heven.
  subst output_rows.
  reflexivity.
Qed.

Lemma filter_even_step_keep_149_valid : forall rows i output_rows,
  0 <= i < Zlength rows ->
  filter_even_state_149 rows i output_rows ->
  even_row_z_149 (Znth i rows nil) = false ->
  filter_even_state_149 rows (i + 1) output_rows.
Proof.
  intros rows i output_rows Hi [Hrange Hstate] Heven.
  split; [lia|].
  unfold filter_even_prefix_149 in *.
  rewrite filter_even_prefix_149_snoc by lia.
  rewrite filter_even_rows_149_app_keep by exact Heven.
  exact Hstate.
Qed.

Lemma filter_even_step_take_149_intro : forall rows i output_rows,
  0 <= i < Zlength rows ->
  filter_even_state_149 rows i output_rows ->
  even_row_z_149 (Znth i rows nil) = true ->
  filter_even_step_take_149 rows i output_rows
    (output_rows ++ [Znth i rows nil]).
Proof.
  unfold filter_even_step_take_149.
  intros rows i output_rows Hi Hstate Heven.
  split; [reflexivity|].
  eapply filter_even_step_take_149_valid; eauto.
Qed.

Lemma filter_even_step_keep_149_intro : forall rows i output_rows,
  0 <= i < Zlength rows ->
  filter_even_state_149 rows i output_rows ->
  even_row_z_149 (Znth i rows nil) = false ->
  filter_even_step_keep_149 rows i output_rows.
Proof.
  unfold filter_even_step_keep_149.
  intros rows i output_rows Hi Hstate Heven.
  eapply filter_even_step_keep_149_valid; eauto.
Qed.

Lemma Z_even_true_of_rem2_149 : forall z,
  0 <= z ->
  Z.rem z 2 = 0 ->
  Z.even z = true.
Proof.
  intros z Hz Hrem.
  apply Z.even_spec.
  rewrite Z.rem_mod_nonneg in Hrem by lia.
  apply (proj1 (Z.mod_divide z 2 ltac:(lia))) in Hrem.
  destruct Hrem as [k Hk].
  exists k.
  lia.
Qed.

Lemma Z_even_false_of_rem2_nonzero_149 : forall z,
  0 <= z ->
  Z.rem z 2 <> 0 ->
  Z.even z = false.
Proof.
  intros z Hz Hrem.
  destruct (Z.even z) eqn:Heven; [| reflexivity].
  exfalso.
  apply Hrem.
  rewrite Z.rem_mod_nonneg by lia.
  apply (proj2 (Z.mod_divide z 2 ltac:(lia))).
  apply Z.even_spec in Heven.
  destruct Heven as [k Hk].
  exists k.
  lia.
Qed.

Lemma filter_even_rows_to_strings_149 : forall rows,
  rows_to_strings_z_149 (filter_even_rows_149 rows) =
  filter has_even_length (rows_to_strings_z_149 rows).
Proof.
  induction rows as [|row rest IH]; simpl; [reflexivity|].
  rewrite <- even_row_has_even_length_149.
  destruct (even_row_z_149 row); simpl; rewrite IH; reflexivity.
Qed.

Lemma filter_even_state_full_149 : forall rows filtered,
  filter_even_state_149 rows (Zlength rows) filtered ->
  rows_to_strings_z_149 filtered =
  filter has_even_length (rows_to_strings_z_149 rows).
Proof.
  intros rows filtered [_ Hfiltered].
  subst filtered.
  unfold filter_even_prefix_149.
  rewrite firstn_all2.
  - apply filter_even_rows_to_strings_149.
  - rewrite Zlength_correct.
    lia.
Qed.

Lemma problem_149_spec_z_of_sorted_filter_valid : forall rows filtered sorted,
  filter_even_state_149 rows (Zlength rows) filtered ->
  Permutation_rows_149 filtered sorted ->
  string_rows_sorted_149 sorted ->
  problem_149_spec_z rows sorted.
Proof.
  intros rows filtered sorted Hfilter Hperm Hsorted.
  unfold problem_149_spec_z, problem_149_spec, string_rows_sorted_149 in *.
  split.
  - rewrite <- filter_even_state_full_149 with (filtered := filtered) by exact Hfilter.
    unfold rows_to_strings_z_149.
    apply Permutation_sym.
    apply Permutation_map.
    exact Hperm.
  - exact Hsorted.
Qed.

Lemma problem_149_spec_z_of_sorted_filter_intro : forall rows filtered sorted,
  problem_149_spec_z_of_sorted_filter rows filtered sorted.
Proof.
  unfold problem_149_spec_z_of_sorted_filter.
  intros rows filtered sorted Hfilter Hperm Hsorted.
  eapply problem_149_spec_z_of_sorted_filter_valid; eauto.
Qed.

Lemma problem_149_spec_z_of_sorted_prefix_intro : forall rows sorted,
  problem_149_spec_z_of_sorted_prefix rows sorted.
Proof.
  unfold problem_149_spec_z_of_sorted_prefix.
  intros rows sorted Hperm Hsorted.
  apply problem_149_spec_z_of_sorted_filter_valid
    with (filtered := filter_even_prefix_149 rows (Zlength rows)); auto.
  split.
  - pose proof (Zlength_nonneg rows).
    lia.
  - reflexivity.
Qed.
