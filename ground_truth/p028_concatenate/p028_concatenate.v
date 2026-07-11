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

Lemma String_length_string_of_list_z_28 : forall l,
  String.length (string_of_list_z_28 l) = List.length l.
Proof.
  induction l as [| x xs IH]; simpl; congruence.
Qed.

Lemma row_string_length_z_28 : forall row,
  Z.of_nat (String.length (row_string_z_28 row)) = row_len_z_28 row.
Proof.
  intros row.
  unfold row_string_z_28, row_len_z_28, string_length.
  rewrite String_length_string_of_list_z_28.
  rewrite Zlength_correct.
  reflexivity.
Qed.

Lemma rows_well_formed_28_row : forall rows n k,
  rows_well_formed_28 rows n ->
  0 <= k < n ->
  let row := Znth k rows nil in
  let payload := row_payload_z_28 row in
  row = c_string payload /\
  valid_string payload /\
  all_ascii payload /\
  string_length payload < INT_MAX /\
  Zlength row = string_length payload + 1.
Proof.
  intros rows n k [Hlen Hwf] Hk row payload.
  specialize (Hwf k Hk).
  destruct Hwf as [Hrow [Hvalid [Hascii Hlt]]].
  split; [exact Hrow|].
  split; [exact Hvalid|].
  split; [exact Hascii|].
  split; [exact Hlt|].
  subst row payload.
  change (Zlength (Znth k rows nil) =
          Zlength (row_payload_z_28 (Znth k rows nil)) + 1).
  rewrite Hrow at 1.
  unfold c_string.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma c_string_payload_prefix_28 : forall payload,
  sublist 0 (string_length payload) (c_string payload) = payload.
Proof.
  intros payload.
  unfold c_string, string_length.
  apply sublist_app_exact1.
Qed.

Lemma row_payload_c_string_28 : forall payload,
  row_payload_z_28 (c_string payload) = payload.
Proof.
  intros payload.
  unfold row_payload_z_28, c_string.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  change (Z.succ 0) with 1.
  replace (Zlength payload + 1 - 1) with (Zlength payload) by lia.
  rewrite Zlength_correct, Nat2Z.id.
  rewrite firstn_app, firstn_all.
  rewrite Nat.sub_diag.
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma c_string_payload_nul_28 : forall payload,
  sublist (string_length payload) (string_length payload + 1)
    (c_string payload) = cons 0 nil.
Proof.
  intros payload.
  unfold c_string, string_length.
  rewrite (sublist_split_app_r (Zlength payload) (Zlength payload + 1)
    (Zlength payload) payload (cons 0 nil)).
  - replace (Zlength payload - Zlength payload) with 0 by lia.
    replace (Zlength payload + 1 - Zlength payload) with 1 by lia.
    apply sublist_self.
    rewrite Zlength_cons, Zlength_nil.
    lia.
  - reflexivity.
  - lia.
Qed.

Lemma total_prefix_state_28_initial : forall rows,
  total_prefix_state_28 rows 0 1.
Proof.
  intros rows.
  unfold total_prefix_state_28, concat_prefix_len_28,
    concat_prefix_payload_28.
  split; [rewrite Zlength_correct; lia|].
  simpl.
  lia.
Qed.

Lemma firstn_succ_Z_28 : forall (rows : list (list Z)) k,
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

Lemma concat_rows_payload_28_app : forall a b,
  concat_rows_payload_28 (a ++ b) =
  concat_rows_payload_28 a ++ concat_rows_payload_28 b.
Proof.
  induction a as [| row rest IH]; simpl; intros b.
  - reflexivity.
  - rewrite IH, app_assoc.
    reflexivity.
Qed.

Lemma concat_prefix_payload_28_step : forall rows k,
  0 <= k < Zlength rows ->
  concat_prefix_payload_28 rows (k + 1) =
  concat_prefix_payload_28 rows k ++ row_payload_z_28 (Znth k rows nil).
Proof.
  intros rows k Hk.
  unfold concat_prefix_payload_28.
  rewrite firstn_succ_Z_28 by exact Hk.
  rewrite concat_rows_payload_28_app.
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma concat_rows_payload_28_firstn_mono_nat : forall rows a b,
  (a <= b)%nat ->
  Zlength (concat_rows_payload_28 (firstn a rows)) <=
  Zlength (concat_rows_payload_28 (firstn b rows)).
Proof.
  induction rows as [| row rest IH]; intros [| a] [| b] Hab; simpl in *; try lia.
  - apply Zlength_nonneg.
  - repeat rewrite Zlength_app.
    specialize (IH a b).
    lia.
Qed.

Lemma concat_prefix_len_monotone_28 : forall rows a b,
  0 <= a <= b ->
  concat_prefix_len_28 rows a <= concat_prefix_len_28 rows b.
Proof.
  intros rows a b Hab.
  unfold concat_prefix_len_28, concat_prefix_payload_28.
  apply concat_rows_payload_28_firstn_mono_nat.
  apply Z2Nat.inj_le; lia.
Qed.

Lemma copy_prefix_state_28_room : forall rows n i k out_l total,
  rows_well_formed_28 rows n ->
  total_prefix_state_28 rows n total ->
  copy_prefix_state_28 rows i k out_l ->
  0 <= i < n ->
  k + row_len_z_28 (Znth i rows nil) < total.
Proof.
  intros rows n i k out_l total Hwf Htotal Hcopy Hi.
  destruct Hwf as [Hrows _].
  unfold total_prefix_state_28 in Htotal.
  unfold copy_prefix_state_28 in Hcopy.
  destruct Htotal as [_ Htotal].
  destruct Hcopy as [_ [Hout Hk]].
  subst total k out_l.
  assert (Hmono:
    concat_prefix_len_28 rows (i + 1) <= concat_prefix_len_28 rows n).
  {
    apply concat_prefix_len_monotone_28.
    lia.
  }
  unfold concat_prefix_len_28 in Hmono.
  rewrite concat_prefix_payload_28_step in Hmono by lia.
  rewrite Zlength_app in Hmono.
  unfold concat_prefix_len_28.
  unfold row_len_z_28, string_length in *.
  lia.
Qed.

Lemma total_prefix_state_28_step : forall rows k total len,
  total_prefix_state_28 rows k total ->
  0 <= k < Zlength rows ->
  len = row_len_z_28 (Znth k rows nil) ->
  total_prefix_state_28 rows (k + 1) (total + len).
Proof.
  intros rows k total len [Hkbounds Htotal] Hk Hlen.
  unfold total_prefix_state_28, concat_prefix_len_28 in *.
  split; [lia|].
  rewrite concat_prefix_payload_28_step by exact Hk.
  rewrite Zlength_app.
  subst total len.
  unfold row_len_z_28, string_length.
  lia.
Qed.

Lemma copy_prefix_state_28_initial : forall rows,
  copy_prefix_state_28 rows 0 0 nil.
Proof.
  intros rows.
  unfold copy_prefix_state_28, concat_prefix_payload_28.
  split; [rewrite Zlength_correct; lia|].
  simpl.
  repeat split; rewrite ?Zlength_nil; reflexivity.
Qed.

Lemma copy_prefix_state_28_step : forall rows k pos out_l bytes,
  copy_prefix_state_28 rows k pos out_l ->
  0 <= k < Zlength rows ->
  bytes = row_payload_z_28 (Znth k rows nil) ->
  copy_prefix_state_28 rows (k + 1) (pos + Zlength bytes) (out_l ++ bytes).
Proof.
  intros rows k pos out_l bytes [Hkbounds [Hout Hpos]] Hk Hbytes.
  unfold copy_prefix_state_28 in *.
  split; [lia|].
  split.
  - rewrite concat_prefix_payload_28_step by exact Hk.
    subst out_l bytes.
    reflexivity.
  - rewrite Zlength_app.
    subst pos bytes.
    lia.
Qed.

Lemma string_of_list_z_28_app : forall a b,
  string_of_list_z_28 (a ++ b) =
  String.append (string_of_list_z_28 a) (string_of_list_z_28 b).
Proof.
  induction a as [| x xs IH]; simpl; intros b; congruence.
Qed.

Lemma string_append_empty_r_28 : forall s,
  String.append s EmptyString = s.
Proof.
  induction s as [| a s IH]; simpl; congruence.
Qed.

Lemma string_of_concat_rows_payload_28 : forall rows,
  string_of_list_z_28 (concat_rows_payload_28 rows) =
  String.concat "" (rows_to_strings_z_28 rows).
Proof.
  induction rows as [| row rest IH]; simpl.
  - reflexivity.
  - unfold row_string_z_28.
    rewrite string_of_list_z_28_app.
    rewrite IH.
    destruct (rows_to_strings_z_28 rest) as [| s ss]; simpl.
    + apply string_append_empty_r_28.
    + reflexivity.
Qed.

Lemma problem_28_spec_z_intro : forall rows out_l,
  out_l = concat_prefix_payload_28 rows (Zlength rows) ->
  problem_28_spec_z rows out_l.
Proof.
  intros rows out_l Hout.
  unfold problem_28_spec_z, problem_28_spec.
  subst out_l.
  unfold concat_prefix_payload_28.
  rewrite firstn_all2.
  - symmetry.
    apply string_of_concat_rows_payload_28.
  - rewrite Zlength_correct.
    rewrite Nat2Z.id.
    lia.
Qed.
