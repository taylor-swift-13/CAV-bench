(* You will be given a string of words separated by commas or spaces. Your task is
to split the string into words and return an array of the words.

For example:
words_string("Hi, my name is John") == ["Hi", "my", "name", "is", "John"]
words_string("One, two, three, four, five, six") == ["One", "two", "three", "four", "five", "six"] *)

Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.



Definition is_delimiter (c : ascii) : bool :=
  match c with
  | ","%char | " "%char => true | _ => false end.

Fixpoint words_string_aux (current_word : list ascii) (input : list ascii) : list (list ascii) :=
  match input with
  | [] => match current_word with [] => [] | _ => [current_word] end
  | c :: cs => if is_delimiter c then
                 match current_word with
                 | [] => words_string_aux [] cs
                 | _ => current_word :: words_string_aux [] cs
                 end
               else words_string_aux (current_word ++ [c]) cs
  end.

Definition words_string_list_impl (s : list ascii) : list (list ascii) :=
  words_string_aux [] s.

Definition words_string (s : string) : list string :=
  map string_of_list_ascii (words_string_list_impl (list_ascii_of_string s)).

(* 输入为仅包含字母、逗号或空格的字符列表 *)
Definition problem_101_pre (s : string) : Prop :=
  let l := list_ascii_of_string s in
  Forall (fun c =>
    let n := nat_of_ascii c in
      (65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122) \/ c = ","%char \/ c = " "%char) l.

Definition problem_101_spec (s : string) (output : list string) : Prop :=
  output = words_string s.
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

Definition ascii_of_z_101 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_101 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_101 c) (string_of_list_z_101 rest)
  end.

Definition row_payload_z_101 (row : list Z) : list Z :=
  firstn (Z.to_nat (Zlength row - 1)) row.

Definition row_string_z_101 (row : list Z) : string :=
  string_of_list_z_101 (row_payload_z_101 row).

Definition rows_to_strings_z_101 (rows : list (list Z)) : list string :=
  map row_string_z_101 rows.

Definition problem_101_pre_z (s : list Z) : Prop :=
  problem_101_pre (string_of_list_z_101 s).

Definition problem_101_spec_z (s : list Z) (rows : list (list Z)) : Prop :=
  problem_101_spec (string_of_list_z_101 s) (rows_to_strings_z_101 rows).

Definition is_delim_z_101 (c : Z) : bool :=
  Z.eqb c 32 || Z.eqb c 44.

Definition valid_words_char_101 (c : Z) : Prop :=
  c = 32 \/ c = 44 \/ (65 <= c <= 90) \/ (97 <= c <= 122).

Definition valid_words_input_101 (s : list Z) : Prop :=
  forall i, 0 <= i < Zlength s -> valid_words_char_101 (Znth i s 0).

Definition word_payload_101 (s : list Z) (start stop : Z) : list Z :=
  sublist start stop s.

Definition word_row_101 (s : list Z) (start stop : Z) : list Z :=
  c_string (word_payload_101 s start stop).

Definition split_step_101
    (st : list (list Z) * list Z) (c : Z) : list (list Z) * list Z :=
  let '(rows, cur) := st in
  if is_delim_z_101 c then
    match cur with
    | [] => (rows, [])
    | _ => (rows ++ [cur], [])
    end
  else (rows, cur ++ [c]).

Fixpoint split_state_nat_101 (n : nat) (s : list Z)
  : list (list Z) * list Z :=
  match n with
  | O => ([], [])
  | S n' =>
      split_step_101
        (split_state_nat_101 n' s)
        (Znth (Z.of_nat n') s 0)
  end.

Definition split_completed_payloads_101 (s : list Z) (i : Z) : list (list Z) :=
  fst (split_state_nat_101 (Z.to_nat i) s).

Definition split_scan_current_101 (s : list Z) (i : Z) : list Z :=
  snd (split_state_nat_101 (Z.to_nat i) s).

Definition split_completed_rows_101 (s : list Z) (i : Z) : list (list Z) :=
  map c_string (split_completed_payloads_101 s i).

Definition words_payloads_101 (s : list Z) : list (list Z) :=
  let '(rows, cur) := split_state_nat_101 (Z.to_nat (Zlength s)) s in
  match cur with
  | [] => rows
  | _ => rows ++ [cur]
  end.

Definition words_output_rows_101 (s : list Z) : list (list Z) :=
  map c_string (words_payloads_101 s).

Definition split_scan_state_101
    (s : list Z) (i start : Z) (rows : list (list Z)) : Prop :=
  0 <= i <= string_length s /\
  rows = split_completed_rows_101 s i /\
  ((split_scan_current_101 s i = [] /\ start = -1) \/
   (0 <= start < i /\ split_scan_current_101 s i = word_payload_101 s start i)).

Fixpoint words_rows_heap_101
    (row_ptrs : list Z) (rows : list (list Z)) : Assertion :=
  match row_ptrs, rows with
  | p :: ps, row :: rs =>
      CharArray.full p (Zlength row) row ** words_rows_heap_101 ps rs
  | _, _ => emp
  end.

Definition split_step_ascii_101
    (st : list (list ascii) * list ascii) (c : ascii)
    : list (list ascii) * list ascii :=
  let '(rows, cur) := st in
  if is_delimiter c then
    match cur with
    | [] => (rows, [])
    | _ => (rows ++ [cur], [])
    end
  else (rows, cur ++ [c]).

Fixpoint split_state_nat_ascii_101 (n : nat) (s : list ascii)
  : list (list ascii) * list ascii :=
  match n with
  | O => ([], [])
  | S n' =>
      split_step_ascii_101
        (split_state_nat_ascii_101 n' s)
        (nth n' s "000"%char)
  end.

Definition split_state_list_ascii_101
    (s : list ascii) (st : list (list ascii) * list ascii)
    : list (list ascii) * list ascii :=
  fold_left (fun acc c => split_step_ascii_101 acc c) s st.

Definition map_state_ascii_101
    (st : list (list Z) * list Z) : list (list ascii) * list ascii :=
  (map (map ascii_of_z_101) (fst st), map ascii_of_z_101 (snd st)).

Lemma words_rows_heap_101_nil :
  emp |-- words_rows_heap_101 nil nil.
Proof.
  simpl.
  entailer!.
Qed.

Lemma words_rows_heap_101_app_single : forall ptrs rows p row,
  Zlength ptrs = Zlength rows ->
  words_rows_heap_101 ptrs rows ** CharArray.full p (Zlength row) row
  |-- words_rows_heap_101 (ptrs ++ [p]) (rows ++ [row]).
Proof.
  intros ptrs rows p row Hlen.
  revert rows Hlen.
  induction ptrs as [| p0 ptrs IH]; intros rows Hlen;
    destruct rows as [| row0 rows]; simpl in *.
  - rewrite derivable1_sepcon_comm.
    entailer!.
  - rewrite Zlength_nil in Hlen.
    rewrite Zlength_cons in Hlen.
    pose proof (Zlength_nonneg rows).
    lia.
  - rewrite Zlength_nil in Hlen.
    rewrite Zlength_cons in Hlen.
    pose proof (Zlength_nonneg ptrs).
    lia.
  - rewrite Zlength_cons in Hlen.
    rewrite Zlength_cons in Hlen.
    assert (Htail : Zlength ptrs = Zlength rows) by lia.
    sep_apply (IH rows Htail).
    cancel.
Qed.

Lemma String_length_string_of_list_z_101 : forall l,
  String.length (string_of_list_z_101 l) = List.length l.
Proof.
  induction l as [| x xs IH]; simpl; congruence.
Qed.

Lemma row_payload_c_string_101 : forall payload,
  row_payload_z_101 (c_string payload) = payload.
Proof.
  intros payload.
  unfold row_payload_z_101, c_string.
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

Lemma rows_to_strings_c_string_101 : forall payloads,
  rows_to_strings_z_101 (map c_string payloads) =
  map string_of_list_z_101 payloads.
Proof.
  induction payloads as [| p ps IH]; simpl; [reflexivity|].
  unfold row_string_z_101.
  rewrite row_payload_c_string_101.
  rewrite IH.
  reflexivity.
Qed.

Lemma Zlength_map_101 : forall {A B : Type} (f : A -> B) (l : list A),
  Zlength (map f l) = Zlength l.
Proof.
  intros.
  repeat rewrite Zlength_correct.
  rewrite length_map.
  reflexivity.
Qed.

Lemma ascii_of_z_101_nat_of_ascii : forall z,
  0 <= z < 128 ->
  nat_of_ascii (ascii_of_z_101 z) = Z.to_nat z.
Proof.
  intros z Hz.
  unfold ascii_of_z_101.
  rewrite nat_ascii_embedding by lia.
  reflexivity.
Qed.

Lemma string_of_list_ascii_map_ascii_of_z_101 : forall s,
  string_of_list_ascii (map ascii_of_z_101 s) = string_of_list_z_101 s.
Proof.
  induction s as [| c cs IH]; simpl; congruence.
Qed.

Lemma list_ascii_of_string_of_list_z_101 : forall s,
  list_ascii_of_string (string_of_list_z_101 s) =
  map ascii_of_z_101 s.
Proof.
  induction s as [| c cs IH]; simpl; congruence.
Qed.

Lemma is_delimiter_code_101 : forall c,
  is_delimiter c =
  (Nat.eqb (nat_of_ascii c) 44 || Nat.eqb (nat_of_ascii c) 32)%bool.
Proof.
  intros [[] [] [] [] [] [] [] []]; reflexivity.
Qed.

Lemma Nat_eqb_Z_to_nat_101 : forall z k,
  0 <= z ->
  0 <= k ->
  (Nat.eqb (Z.to_nat z) (Z.to_nat k)) = Z.eqb z k.
Proof.
  intros z k Hz Hk.
  destruct (Z.eqb_spec z k) as [Heq | Hneq].
  - subst. rewrite Nat.eqb_refl. reflexivity.
  - apply Nat.eqb_neq.
    intro Hnat.
    apply Hneq.
    apply Z2Nat.inj in Hnat; lia.
Qed.

Lemma is_delimiter_ascii_of_z_101 : forall z,
  0 <= z < 128 ->
  is_delimiter (ascii_of_z_101 z) = is_delim_z_101 z.
Proof.
  intros z Hz.
  rewrite is_delimiter_code_101.
  rewrite ascii_of_z_101_nat_of_ascii by lia.
  unfold is_delim_z_101.
  change 44%nat with (Z.to_nat 44).
  change 32%nat with (Z.to_nat 32).
  rewrite !Nat_eqb_Z_to_nat_101 by lia.
  rewrite Bool.orb_comm.
  reflexivity.
Qed.

Lemma nth_map_ascii_Znth_101 : forall s n,
  (n < List.length s)%nat ->
  nth n (map ascii_of_z_101 s) "000"%char =
  ascii_of_z_101 (Znth (Z.of_nat n) s 0).
Proof.
  induction s as [| x xs IH]; intros [| n] Hlt; simpl in *; try lia.
  - reflexivity.
  - rewrite Znth_cons by lia.
    replace (Z.pos (Pos.of_succ_nat n) - 1) with (Z.of_nat n) by lia.
    apply IH. lia.
Qed.

Lemma split_step_ascii_map_101 : forall st c,
  0 <= c < 128 ->
  split_step_ascii_101 (map_state_ascii_101 st) (ascii_of_z_101 c) =
  map_state_ascii_101 (split_step_101 st c).
Proof.
  intros [rows cur] c Hc.
  unfold split_step_ascii_101, map_state_ascii_101, split_step_101; simpl.
  rewrite is_delimiter_ascii_of_z_101 by lia.
  destruct (is_delim_z_101 c); destruct cur as [| x xs]; simpl;
    rewrite ?map_app; reflexivity.
Qed.

Lemma split_state_nat_ascii_map_101 : forall n s,
  (n <= List.length s)%nat ->
  all_ascii s ->
  split_state_nat_ascii_101 n (map ascii_of_z_101 s) =
  map_state_ascii_101 (split_state_nat_101 n s).
Proof.
  induction n as [| n IH]; intros s Hlen Hascii; simpl.
  - reflexivity.
  - rewrite IH by (try exact Hascii; lia).
    rewrite nth_map_ascii_Znth_101 by lia.
    rewrite split_step_ascii_map_101.
    + reflexivity.
    + pose proof (Hascii (Z.of_nat n) ltac:(rewrite Zlength_correct; lia)).
      lia.
Qed.

Lemma split_state_nat_ascii_step_101 : forall s n,
  (n < List.length s)%nat ->
  split_state_nat_ascii_101 (S n) s =
  split_step_ascii_101 (split_state_nat_ascii_101 n s) (nth n s "000"%char).
Proof.
  reflexivity.
Qed.

Lemma skipn_nth_cons_101 : forall {A : Type} (s : list A) n d,
  (n < List.length s)%nat ->
  skipn n s = nth n s d :: skipn (S n) s.
Proof.
  induction s as [| x xs IH]; intros [| n] d Hlen; simpl in *; try lia.
  - reflexivity.
  - apply IH. lia.
Qed.

Lemma words_string_aux_split_state_nat_ascii_101 : forall s n rows cur,
  (n <= List.length s)%nat ->
  split_state_nat_ascii_101 n s = (rows, cur) ->
  words_string_aux [] s = rows ++ words_string_aux cur (skipn n s).
Proof.
  induction n as [| n IH]; intros rows cur Hlen Hst.
  - simpl in Hst. inversion Hst; subst. reflexivity.
  - assert (Hnlen : (n < List.length s)%nat) by lia.
    destruct (split_state_nat_ascii_101 n s) as [rows0 cur0] eqn:Hprev.
    specialize (IH rows0 cur0 ltac:(lia) eq_refl).
    rewrite IH.
    rewrite (skipn_nth_cons_101 s n "000"%char) by lia.
    simpl in Hst.
    rewrite Hprev in Hst.
    unfold split_step_ascii_101 in Hst.
    destruct (is_delimiter (nth n s "000"%char)) eqn:Hdelim.
    + destruct cur0 as [| c cs].
      * inversion Hst; subst.
        simpl. rewrite Hdelim. reflexivity.
      * inversion Hst; subst.
        simpl. rewrite Hdelim. rewrite <- app_assoc. reflexivity.
    + inversion Hst; subst.
      simpl. rewrite Hdelim. reflexivity.
Qed.

Lemma words_string_list_impl_split_state_nat_ascii_101 : forall s,
  words_string_list_impl s =
  let '(rows, cur) := split_state_nat_ascii_101 (List.length s) s in
  match cur with
  | [] => rows
  | _ => rows ++ [cur]
  end.
Proof.
  intros s.
  unfold words_string_list_impl.
  destruct (split_state_nat_ascii_101 (List.length s) s) as [rows cur] eqn:Hst.
  rewrite (words_string_aux_split_state_nat_ascii_101 s (List.length s) rows cur)
    by (try exact Hst; lia).
  rewrite skipn_all.
  destruct cur; rewrite ?app_nil_r; reflexivity.
Qed.

Lemma map_ascii_words_payloads_101 : forall s,
  all_ascii s ->
  words_string_list_impl (map ascii_of_z_101 s) =
  map (map ascii_of_z_101) (words_payloads_101 s).
Proof.
  intros s Hascii.
  rewrite words_string_list_impl_split_state_nat_ascii_101.
  rewrite length_map.
  rewrite split_state_nat_ascii_map_101.
  - unfold words_payloads_101, map_state_ascii_101.
    rewrite Zlength_correct, Nat2Z.id.
    destruct (split_state_nat_101 (List.length s) s) as [rows cur].
    simpl.
    destruct cur; rewrite ?map_app; reflexivity.
  - lia.
  - exact Hascii.
Qed.

Lemma problem_101_spec_z_words_output_rows_101 : forall s,
  all_ascii s ->
  problem_101_spec_z s (words_output_rows_101 s).
Proof.
  intros s Hascii.
  unfold problem_101_spec_z, problem_101_spec, words_string,
    words_output_rows_101.
  rewrite rows_to_strings_c_string_101.
  rewrite list_ascii_of_string_of_list_z_101.
  rewrite map_ascii_words_payloads_101 by exact Hascii.
  rewrite map_map.
  apply map_ext.
  intro row.
  rewrite string_of_list_ascii_map_ascii_of_z_101.
  reflexivity.
Qed.

Lemma split_state_nat_101_rows_bound : forall n s rows cur,
  split_state_nat_101 n s = (rows, cur) ->
  Zlength rows <= Z.of_nat n.
Proof.
  induction n as [| n IH]; intros s rows cur Hst; simpl in Hst.
  - inversion Hst; subst. rewrite Zlength_nil. lia.
  - destruct (split_state_nat_101 n s) as [rows0 cur0] eqn:Hprev.
    unfold split_step_101 in Hst.
    destruct (is_delim_z_101 (Znth (Z.of_nat n) s 0)).
    + destruct cur0 as [| c cs]; inversion Hst; subst.
      * specialize (IH s rows [] Hprev). lia.
      * rewrite Zlength_app, Zlength_cons, Zlength_nil.
        specialize (IH s rows0 (c :: cs) Hprev). lia.
    + inversion Hst; subst.
      specialize (IH s rows cur0 Hprev).
      lia.
Qed.

Lemma Zlength_words_output_rows_101_le : forall s,
  Zlength (words_output_rows_101 s) <= Zlength s + 1.
Proof.
  intros s.
  unfold words_output_rows_101, words_payloads_101.
  destruct (split_state_nat_101 (Z.to_nat (Zlength s)) s) as [rows cur] eqn:Hst.
  destruct cur as [| c cs].
  - rewrite Zlength_map_101.
    pose proof (split_state_nat_101_rows_bound _ _ _ _ Hst).
    rewrite Z2Nat.id in H by (pose proof (Zlength_nonneg s); lia).
    lia.
  - rewrite Zlength_map_101, Zlength_app, Zlength_cons, Zlength_nil.
    pose proof (split_state_nat_101_rows_bound _ _ _ _ Hst).
    rewrite Z2Nat.id in H by (pose proof (Zlength_nonneg s); lia).
    lia.
Qed.

Lemma split_state_nat_101_step : forall i s,
  0 <= i ->
  split_state_nat_101 (Z.to_nat (i + 1)) s =
  split_step_101 (split_state_nat_101 (Z.to_nat i) s) (Znth i s 0).
Proof.
  intros i s Hi.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  reflexivity.
Qed.

Lemma split_completed_rows_101_step_cons : forall s i rows cur,
  0 <= i ->
  split_state_nat_101 (Z.to_nat i) s = (rows, cur) ->
  is_delim_z_101 (Znth i s 0) = true ->
  cur <> [] ->
  split_completed_rows_101 s (i + 1) =
  map c_string rows ++ [c_string cur].
Proof.
  intros s i rows cur Hi Hst Hdelim Hcur.
  unfold split_completed_rows_101, split_completed_payloads_101.
  rewrite split_state_nat_101_step by lia.
  rewrite Hst.
  unfold split_step_101.
  rewrite Hdelim.
  destruct cur; [contradiction|].
  simpl.
  rewrite map_app.
  reflexivity.
Qed.

Lemma split_completed_rows_101_step_empty : forall s i rows,
  0 <= i ->
  split_state_nat_101 (Z.to_nat i) s = (rows, []) ->
  is_delim_z_101 (Znth i s 0) = true ->
  split_completed_rows_101 s (i + 1) = map c_string rows.
Proof.
  intros s i rows Hi Hst Hdelim.
  unfold split_completed_rows_101, split_completed_payloads_101.
  rewrite split_state_nat_101_step by lia.
  rewrite Hst.
  unfold split_step_101.
  rewrite Hdelim.
  reflexivity.
Qed.

Lemma split_completed_rows_101_step_nondelim : forall s i rows cur,
  0 <= i ->
  split_state_nat_101 (Z.to_nat i) s = (rows, cur) ->
  is_delim_z_101 (Znth i s 0) = false ->
  split_completed_rows_101 s (i + 1) = map c_string rows.
Proof.
  intros s i rows cur Hi Hst Hdelim.
  unfold split_completed_rows_101, split_completed_payloads_101.
  rewrite split_state_nat_101_step by lia.
  rewrite Hst.
  unfold split_step_101.
  rewrite Hdelim.
  reflexivity.
Qed.

Lemma split_scan_current_101_step_nondelim : forall s i rows cur,
  0 <= i ->
  split_state_nat_101 (Z.to_nat i) s = (rows, cur) ->
  is_delim_z_101 (Znth i s 0) = false ->
  split_scan_current_101 s (i + 1) = cur ++ [Znth i s 0].
Proof.
  intros s i rows cur Hi Hst Hdelim.
  unfold split_scan_current_101.
  rewrite split_state_nat_101_step by lia.
  rewrite Hst.
  unfold split_step_101.
  rewrite Hdelim.
  reflexivity.
Qed.

Lemma split_scan_current_101_step_delim : forall s i rows cur,
  0 <= i ->
  split_state_nat_101 (Z.to_nat i) s = (rows, cur) ->
  is_delim_z_101 (Znth i s 0) = true ->
  split_scan_current_101 s (i + 1) = [].
Proof.
  intros s i rows cur Hi Hst Hdelim.
  unfold split_scan_current_101.
  rewrite split_state_nat_101_step by lia.
  rewrite Hst.
  unfold split_step_101.
  rewrite Hdelim.
  destruct cur; reflexivity.
Qed.

Lemma word_payload_101_step : forall s start i,
  0 <= start /\ start <= i /\ i < Zlength s ->
  word_payload_101 s start (i + 1) =
  word_payload_101 s start i ++ [Znth i s 0].
Proof.
  intros s start i Hbounds.
  unfold word_payload_101.
  rewrite (sublist_split start (i + 1) i s) by lia.
  replace (sublist i (i + 1) s) with [Znth i s 0].
  - reflexivity.
  - symmetry.
    apply sublist_single.
    lia.
Qed.

Lemma c_string_Znth_before_101 : forall s i,
  0 <= i < Zlength s ->
  Znth i (c_string s) 0 = Znth i s 0.
Proof.
  intros s i Hi.
  unfold c_string.
  rewrite app_Znth1 by lia.
  reflexivity.
Qed.

Lemma Zlength_word_payload_101 : forall s start stop,
  0 <= start <= stop ->
  stop <= Zlength s ->
  Zlength (word_payload_101 s start stop) = stop - start.
Proof.
  intros s start stop Hbounds Hstop.
  unfold word_payload_101.
  rewrite Zlength_sublist by lia.
  lia.
Qed.

Lemma word_payload_101_empty : forall s start,
  word_payload_101 s start start = [].
Proof.
  intros s start.
  unfold word_payload_101.
  apply sublist_nil.
  lia.
Qed.

Lemma word_payload_101_step_offset_c_string : forall s start k,
  0 <= start ->
  0 <= k ->
  start + k < Zlength s ->
  word_payload_101 s start (start + (k + 1)) =
  word_payload_101 s start (start + k) ++
    [Znth (start + k) (c_string s) 0].
Proof.
  intros s start k Hstart Hk Hlt.
  replace (start + (k + 1)) with ((start + k) + 1) by lia.
  rewrite word_payload_101_step by lia.
  rewrite c_string_Znth_before_101 by lia.
  reflexivity.
Qed.

Lemma word_row_101_unfold : forall s start stop,
  word_row_101 s start stop =
  word_payload_101 s start stop ++ [0].
Proof.
  intros.
  unfold word_row_101, c_string.
  reflexivity.
Qed.

Lemma split_scan_state_101_initial : forall s,
  split_scan_state_101 s 0 (-1) [].
Proof.
  intros s.
  unfold split_scan_state_101, split_completed_rows_101,
    split_completed_payloads_101, split_scan_current_101, string_length.
  simpl.
  split; [rewrite Zlength_correct; lia|].
  split; [reflexivity|].
  left.
  split; reflexivity.
Qed.

Lemma is_delim_z_101_true_32 : forall s i,
  0 <= i < Zlength s ->
  Znth i (c_string s) 0 = 32 ->
  is_delim_z_101 (Znth i s 0) = true.
Proof.
  intros s i Hi H.
  unfold is_delim_z_101.
  rewrite <- (c_string_Znth_before_101 s i) by lia.
  rewrite H.
  reflexivity.
Qed.

Lemma is_delim_z_101_true_44 : forall s i,
  0 <= i < Zlength s ->
  Znth i (c_string s) 0 = 44 ->
  is_delim_z_101 (Znth i s 0) = true.
Proof.
  intros s i Hi H.
  unfold is_delim_z_101.
  rewrite <- (c_string_Znth_before_101 s i) by lia.
  rewrite H.
  reflexivity.
Qed.

Lemma is_delim_z_101_false_from_neq : forall s i,
  0 <= i < Zlength s ->
  Znth i (c_string s) 0 <> 32 ->
  Znth i (c_string s) 0 <> 44 ->
  is_delim_z_101 (Znth i s 0) = false.
Proof.
  intros s i Hi H32 H44.
  unfold is_delim_z_101.
  rewrite <- (c_string_Znth_before_101 s i) by lia.
  destruct (Z.eqb_spec (Znth i (c_string s) 0) 32); [congruence|].
  destruct (Z.eqb_spec (Znth i (c_string s) 0) 44); [congruence|].
  reflexivity.
Qed.

Lemma split_scan_state_101_current_nonempty : forall s i start rows,
  split_scan_state_101 s i start rows ->
  0 <= start < i ->
  split_scan_current_101 s i = word_payload_101 s start i.
Proof.
  intros s i start rows Hstate Hstart.
  unfold split_scan_state_101 in Hstate.
  destruct Hstate as [_ [_ [[_ Hbad] | [_ Hcur]]]].
  - lia.
  - exact Hcur.
Qed.

Lemma split_scan_state_101_step_delim_nonempty : forall s i start rows,
  split_scan_state_101 s i start rows ->
  0 <= start < i ->
  is_delim_z_101 (Znth i s 0) = true ->
  i < Zlength s ->
  split_scan_state_101 s (i + 1) (-1)
    (rows ++ [word_row_101 s start i]).
Proof.
  intros s i start rows Hstate Hstart Hdelim Hi.
  unfold split_scan_state_101 in *.
  destruct Hstate as [Hbounds [Hrows Hcur_cases]].
  destruct Hcur_cases as [[Hcur_empty Hstart_bad] | [Hstart2 Hcur]]; [lia|].
  split; [unfold string_length in *; lia|].
  split.
  - unfold split_completed_rows_101, split_completed_payloads_101,
      split_scan_current_101 in *.
    destruct (split_state_nat_101 (Z.to_nat i) s) as [payloads cur] eqn:Hst.
    simpl in Hcur.
    simpl in Hrows; subst rows.
    rewrite split_state_nat_101_step by lia.
    rewrite Hst.
    unfold split_step_101.
    rewrite Hdelim.
    destruct cur as [| c cs].
    + simpl in Hcur.
      assert (Zlength (word_payload_101 s start i) = i - start).
      { apply Zlength_word_payload_101; lia. }
      rewrite <- Hcur in H.
      rewrite Zlength_nil in H.
      lia.
    + simpl.
      unfold word_row_101.
      rewrite map_app.
      rewrite Hcur.
      reflexivity.
  - left.
    unfold split_scan_current_101.
    rewrite split_state_nat_101_step by lia.
    unfold split_scan_current_101 in Hcur.
    destruct (split_state_nat_101 (Z.to_nat i) s) as [payloads cur] eqn:Hst.
    simpl in Hcur.
    unfold split_step_101.
    rewrite Hdelim.
    destruct cur; split; reflexivity.
Qed.

Lemma split_scan_state_101_step_delim_empty : forall s i rows,
  split_scan_state_101 s i (-1) rows ->
  is_delim_z_101 (Znth i s 0) = true ->
  i < Zlength s ->
  split_scan_state_101 s (i + 1) (-1) rows.
Proof.
  intros s i rows Hstate Hdelim Hi.
  unfold split_scan_state_101 in *.
  destruct Hstate as [Hbounds [Hrows Hcur_cases]].
  destruct Hcur_cases as [[Hcur_empty Hstart] | [Hbad _]]; [|lia].
  subst.
  split; [unfold string_length in *; lia|].
  split.
  - unfold split_completed_rows_101, split_completed_payloads_101,
      split_scan_current_101 in *.
    destruct (split_state_nat_101 (Z.to_nat i) s) as [payloads cur] eqn:Hst.
    simpl in Hcur_empty.
    rewrite split_state_nat_101_step by lia.
    rewrite Hst.
    unfold split_step_101.
    rewrite Hdelim.
    destruct cur; [reflexivity|congruence].
  - left.
    unfold split_scan_current_101.
    rewrite split_state_nat_101_step by lia.
    unfold split_scan_current_101 in Hcur_empty.
    destruct (split_state_nat_101 (Z.to_nat i) s) as [payloads cur] eqn:Hst.
    simpl in Hcur_empty.
    unfold split_step_101.
    rewrite Hdelim.
    destruct cur; [split; reflexivity|congruence].
Qed.

Lemma split_scan_state_101_step_nondelim_continue : forall s i start rows,
  split_scan_state_101 s i start rows ->
  0 <= start < i ->
  is_delim_z_101 (Znth i s 0) = false ->
  i < Zlength s ->
  split_scan_state_101 s (i + 1) start rows.
Proof.
  intros s i start rows Hstate Hstart Hdelim Hi.
  unfold split_scan_state_101 in *.
  destruct Hstate as [Hbounds [Hrows Hcur_cases]].
  destruct Hcur_cases as [[_ Hbad] | [Hstart2 Hcur]]; [lia|].
  split; [unfold string_length in *; lia|].
  split.
  - unfold split_completed_rows_101, split_completed_payloads_101,
      split_scan_current_101 in *.
    destruct (split_state_nat_101 (Z.to_nat i) s) as [payloads cur] eqn:Hst.
    simpl in Hcur.
    simpl in Hrows; subst rows.
    rewrite split_state_nat_101_step by lia.
    rewrite Hst.
    unfold split_step_101.
    rewrite Hdelim.
    reflexivity.
  - right.
    split; [lia|].
    unfold split_scan_current_101.
    rewrite split_state_nat_101_step by lia.
    unfold split_scan_current_101 in Hcur.
    destruct (split_state_nat_101 (Z.to_nat i) s) as [payloads cur] eqn:Hst.
    simpl in Hcur.
    unfold split_step_101.
    rewrite Hdelim.
    rewrite Hcur.
    rewrite word_payload_101_step by lia.
    reflexivity.
Qed.

Lemma split_scan_state_101_step_nondelim_start : forall s i rows,
  split_scan_state_101 s i (-1) rows ->
  is_delim_z_101 (Znth i s 0) = false ->
  i < Zlength s ->
  split_scan_state_101 s (i + 1) i rows.
Proof.
  intros s i rows Hstate Hdelim Hi.
  unfold split_scan_state_101 in *.
  destruct Hstate as [Hbounds [Hrows Hcur_cases]].
  destruct Hcur_cases as [[Hcur_empty Hstart] | [Hbad _]]; [|lia].
  subst.
  split; [unfold string_length in *; lia|].
  split.
  - unfold split_completed_rows_101, split_completed_payloads_101,
      split_scan_current_101 in *.
    destruct (split_state_nat_101 (Z.to_nat i) s) as [payloads cur] eqn:Hst.
    simpl in Hcur_empty.
    rewrite split_state_nat_101_step by lia.
    rewrite Hst.
    unfold split_step_101.
    rewrite Hdelim.
    reflexivity.
  - right.
    split; [lia|].
    unfold split_scan_current_101.
    rewrite split_state_nat_101_step by lia.
    unfold split_scan_current_101 in Hcur_empty.
    destruct (split_state_nat_101 (Z.to_nat i) s) as [payloads cur] eqn:Hst.
    simpl in Hcur_empty.
    unfold split_step_101.
    rewrite Hdelim.
    subst cur.
    simpl.
    unfold word_payload_101.
    replace (sublist i (i + 1) s) with [Znth i s 0].
    + reflexivity.
    + symmetry; apply sublist_single; lia.
Qed.

Lemma split_scan_state_101_final_empty : forall s rows,
  split_scan_state_101 s (Zlength s) (-1) rows ->
  rows = words_output_rows_101 s.
Proof.
  intros s rows Hstate.
  unfold split_scan_state_101 in Hstate.
  destruct Hstate as [_ [Hrows Hcur_cases]].
  destruct Hcur_cases as [[Hcur Hstart] | [Hbad _]]; [| lia].
  subst rows.
  unfold words_output_rows_101, words_payloads_101,
    split_completed_rows_101, split_completed_payloads_101 in *.
  unfold split_scan_current_101 in Hcur.
  destruct (split_state_nat_101 (Z.to_nat (Zlength s)) s) as [payloads cur].
  simpl in *.
  subst cur.
  reflexivity.
Qed.

Lemma split_scan_state_101_final_nonempty : forall s start rows,
  split_scan_state_101 s (Zlength s) start rows ->
  0 <= start < Zlength s ->
  rows ++ [word_row_101 s start (Zlength s)] = words_output_rows_101 s.
Proof.
  intros s start rows Hstate Hstart.
  unfold split_scan_state_101 in Hstate.
  destruct Hstate as [_ [Hrows Hcur_cases]].
  destruct Hcur_cases as [[_ Hbad] | [_ Hcur]]; [lia|].
  subst rows.
  unfold words_output_rows_101, words_payloads_101,
    split_completed_rows_101, split_completed_payloads_101 in *.
  unfold split_scan_current_101 in Hcur.
  destruct (split_state_nat_101 (Z.to_nat (Zlength s)) s) as [payloads cur].
  simpl in *.
  destruct cur as [| c cs].
  - assert (Zlength (word_payload_101 s start (Zlength s)) =
      Zlength s - start).
    { apply Zlength_word_payload_101; lia. }
    rewrite <- Hcur in H.
    rewrite Zlength_nil in H.
    lia.
  - unfold word_row_101.
    rewrite <- Hcur.
    simpl.
    rewrite map_app.
    reflexivity.
Qed.
