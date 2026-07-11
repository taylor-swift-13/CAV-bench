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

Lemma sublist_0_firstn_14 : forall {A : Type} hi (l : list A),
  0 <= hi ->
  sublist 0 hi l = firstn (Z.to_nat hi) l.
Proof.
  intros A hi l _.
  unfold sublist.
  reflexivity.
Qed.

Fixpoint prefix_payloads_nat_14 (s : list Z) (n : nat) : list (list Z) :=
  match n with
  | O => []
  | S k => prefix_payloads_nat_14 s k ++ [firstn (S k) s]
  end.

Lemma prefix_payloads_nat_14_length : forall s n,
  List.length (prefix_payloads_nat_14 s n) = n.
Proof.
  induction n as [| n IH]; simpl; auto.
  rewrite app_length; simpl; lia.
Qed.

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

Lemma prefix_rows_heap_14_nil :
  emp |-- prefix_rows_heap_14 nil nil.
Proof.
  simpl.
  entailer!.
Qed.

Lemma prefix_rows_heap_14_app_single : forall ptrs rows p row,
  Zlength ptrs = Zlength rows ->
  prefix_rows_heap_14 ptrs rows ** CharArray.full p (Zlength row) row
  |-- prefix_rows_heap_14 (ptrs ++ [p]) (rows ++ [row]).
Proof.
  intros ptrs rows p row Hlen.
  revert rows Hlen.
  induction ptrs as [| p0 ptrs IH]; intros rows Hlen;
    destruct rows as [| row0 rows]; simpl in *.
  - rewrite derivable1_sepcon_comm.
    entailer!.
  - exfalso.
    rewrite Zlength_nil in Hlen. rewrite Zlength_cons in Hlen.
    pose proof (Zlength_nonneg rows). lia.
  - exfalso.
    rewrite Zlength_nil in Hlen. rewrite Zlength_cons in Hlen.
    pose proof (Zlength_nonneg ptrs). lia.
  - rewrite Zlength_cons in Hlen.
    rewrite Zlength_cons in Hlen.
    assert (Htail : Zlength ptrs = Zlength rows) by lia.
    sep_apply (IH rows Htail).
    cancel.
Qed.

Lemma chararray_adjacent_segs_to_full_14 : forall p mid hi l1 l2,
  0 <= mid <= hi ->
  CharArray.seg p 0 mid l1 ** CharArray.seg p mid hi l2
  |-- CharArray.full p hi (l1 ++ l2).
Proof.
  intros p mid hi l1 l2 Hbounds.
  sep_apply (CharArray.seg_merge_to_seg p 0 mid hi l1 l2 Hbounds).
  sep_apply_l_atomic (CharArray.seg_to_full p 0 hi (l1 ++ l2)).
  replace (p + 0 * sizeof(CHAR)) with p by lia.
  replace (hi - 0) with hi by lia.
  entailer!.
Qed.

Definition valid_prefixes_14 (s : list Z) : Prop :=
  string_length s + 2 < INT_MAX.

Definition problem_14_pre_z (s : list Z) : Prop :=
  problem_14_pre (string_of_list_z_14 s).

Definition problem_14_spec_z (s : list Z) (rows : list (list Z)) : Prop :=
  problem_14_spec (string_of_list_z_14 s) (rows_to_strings_z_14 rows).

Lemma String_length_string_of_list_z_14 : forall l,
  String.length (string_of_list_z_14 l) = List.length l.
Proof.
  induction l as [| x xs IH]; simpl; congruence.
Qed.

Lemma Zlength_prefix_row_payload_14 : forall s i,
  0 <= i < string_length s ->
  Zlength (prefix_row_payload_14 s i) = i + 1.
Proof.
  intros s i Hi.
  unfold prefix_row_payload_14, string_length in *.
  rewrite Zlength_sublist by lia.
  lia.
Qed.

Lemma all_ascii_prefix_row_payload_14 : forall s i,
  all_ascii s ->
  0 <= i < string_length s ->
  all_ascii (prefix_row_payload_14 s i).
Proof.
  intros s i Hascii Hi k Hk.
  pose proof (Zlength_prefix_row_payload_14 s i Hi) as Hlen.
  unfold prefix_row_payload_14.
  rewrite Znth_sublist0 by lia.
  apply Hascii.
  unfold string_length in Hi.
  lia.
Qed.

Lemma prefix_row_payload_c_string_14 : forall s i,
  0 <= i < string_length s ->
  sublist 0 (i + 1) (c_string s) = prefix_row_payload_14 s i.
Proof.
  intros s i Hi.
  unfold prefix_row_payload_14, c_string, string_length in *.
  apply sublist_split_app_l; lia.
Qed.

Lemma prefix_row_payload_suffix_c_string_14 : forall s i n,
  0 <= i < n ->
  n = string_length s ->
  prefix_row_payload_14 s i ++ sublist (i + 1) (n + 1) (c_string s) =
  c_string s.
Proof.
  intros s i n Hi Hn.
  subst n.
  rewrite <- (prefix_row_payload_c_string_14 s i) by lia.
  rewrite <- (sublist_split 0 (string_length s + 1) (i + 1) (c_string s)).
  2: lia.
  2: {
    assert (Hc_len : Zlength (c_string s) = string_length s + 1).
    {
      unfold c_string, string_length.
      rewrite Zlength_app, Zlength_cons, Zlength_nil.
      lia.
    }
    rewrite Hc_len.
    pose proof (Zlength_nonneg s).
    lia.
  }
  unfold c_string, string_length.
  rewrite sublist_self.
  - reflexivity.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
Qed.

Lemma prefix_rows_state_14_initial : forall s,
  prefix_rows_state_14 s 0 nil.
Proof.
  intros s.
  unfold prefix_rows_state_14, prefix_rows_14, string_length.
  split; [rewrite Zlength_correct; lia|].
  reflexivity.
Qed.

Lemma prefix_payloads_nat_14_snoc : forall s n,
  prefix_payloads_nat_14 s (S n) =
  prefix_payloads_nat_14 s n ++ [firstn (S n) s].
Proof.
  reflexivity.
Qed.

Lemma prefix_rows_14_step : forall s i,
  0 <= i < string_length s ->
  prefix_rows_14 s (i + 1) =
  prefix_rows_14 s i ++ [prefix_row_14 s i].
Proof.
  intros s i Hi.
  unfold prefix_rows_14, prefix_row_14, prefix_row_payload_14.
  assert (Hsucc: Z.to_nat (i + 1) = S (Z.to_nat i)).
  {
    apply Nat2Z.inj.
    rewrite Z2Nat.id by lia.
    rewrite Nat2Z.inj_succ, Z2Nat.id by lia.
    lia.
  }
  rewrite Hsucc.
  simpl.
  rewrite map_app.
  simpl.
  rewrite sublist_0_firstn_14 by lia.
  rewrite Hsucc.
  reflexivity.
Qed.

Lemma prefix_rows_state_14_step : forall s i rows,
  prefix_rows_state_14 s i rows ->
  0 <= i < string_length s ->
  prefix_rows_state_14 s (i + 1) (rows ++ [prefix_row_14 s i]).
Proof.
  intros s i rows [Hbounds Hrows] Hi.
  split; [lia|].
  subst rows.
  symmetry.
  apply prefix_rows_14_step; exact Hi.
Qed.

Lemma Zlength_prefix_rows_14 : forall s n,
  0 <= n ->
  Zlength (prefix_rows_14 s n) = n.
Proof.
  intros s n Hn.
  unfold prefix_rows_14.
  rewrite Zlength_correct, map_length, prefix_payloads_nat_14_length.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.

Lemma prefix_rows_state_14_Zlength : forall s n rows,
  prefix_rows_state_14 s n rows ->
  Zlength rows = n.
Proof.
  intros s n rows [Hbounds Hrows].
  subst rows.
  apply Zlength_prefix_rows_14.
  lia.
Qed.

Lemma row_payload_c_string_14 : forall payload,
  row_payload_z_14 (c_string payload) = payload.
Proof.
  intros payload.
  unfold row_payload_z_14, c_string.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  rewrite Zlength_correct.
  replace (Z.of_nat (List.length payload) + Z.succ 0 - 1)
    with (Z.of_nat (List.length payload)) by lia.
  rewrite Nat2Z.id.
  replace (List.length payload) with (List.length payload + 0)%nat by lia.
  rewrite firstn_app_2.
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma row_string_prefix_row_14 : forall s i,
  row_string_z_14 (prefix_row_14 s i) =
  string_of_list_z_14 (prefix_row_payload_14 s i).
Proof.
  intros s i.
  unfold row_string_z_14, prefix_row_14.
  rewrite row_payload_c_string_14.
  reflexivity.
Qed.

Lemma rows_to_strings_prefix_rows_14 : forall s n,
  rows_to_strings_z_14 (prefix_rows_14 s n) =
  map string_of_list_z_14 (prefix_payloads_nat_14 s (Z.to_nat n)).
Proof.
  intros s n.
  unfold rows_to_strings_z_14, prefix_rows_14.
  rewrite map_map.
  apply map_ext.
  intros payload.
  unfold row_string_z_14.
  rewrite row_payload_c_string_14.
  reflexivity.
Qed.

Lemma string_of_list_z_14_firstn_prefix : forall s n,
  String.prefix
    (string_of_list_z_14 (firstn n s))
    (string_of_list_z_14 s) = true.
Proof.
  induction s as [| c rest IH]; intros [| n]; simpl; auto.
  destruct (ascii_dec (ascii_of_z_14 c) (ascii_of_z_14 c)).
  - apply IH.
  - contradiction.
Qed.

Lemma nth_map_prefix_payloads_nat_14 : forall s n i,
  (i < n)%nat ->
  nth i
    (map string_of_list_z_14 (prefix_payloads_nat_14 s n))
    "0" =
  string_of_list_z_14 (firstn (S i) s).
Proof.
  induction n as [| n IH]; intros i Hi; [lia|].
  rewrite prefix_payloads_nat_14_snoc, map_app.
  destruct (Nat.eq_dec i n) as [Heq|Hneq].
  - subst i.
    rewrite app_nth2.
    + rewrite map_length, prefix_payloads_nat_14_length.
      replace (n - n)%nat with O by lia.
      reflexivity.
    + rewrite map_length, prefix_payloads_nat_14_length; lia.
  - rewrite app_nth1.
    + apply IH; lia.
    + rewrite map_length, prefix_payloads_nat_14_length; lia.
Qed.

Lemma prefix_rows_14_spec : forall s rows,
  prefix_rows_state_14 s (string_length s) rows ->
  problem_14_spec_z s rows.
Proof.
  intros s rows [Hbounds Hrows].
  unfold problem_14_spec_z, problem_14_spec.
  subst rows.
  rewrite rows_to_strings_prefix_rows_14.
  assert (Hznat: Z.to_nat (string_length s) = List.length s).
  {
    unfold string_length.
    rewrite Zlength_correct, Nat2Z.id.
    reflexivity.
  }
  rewrite Hznat.
  rewrite String_length_string_of_list_z_14.
  destruct (List.length s) as [| len] eqn:Hlen.
  - left.
    split; reflexivity.
  - right.
    split.
    + lia.
    + split.
      * rewrite map_length, prefix_payloads_nat_14_length.
        reflexivity.
      * intros i Hi.
        rewrite nth_map_prefix_payloads_nat_14 by lia.
        split.
        -- rewrite String_length_string_of_list_z_14.
           rewrite firstn_length.
           lia.
        -- apply string_of_list_z_14_firstn_prefix.
Qed.
