(* Given a string s and a natural number n, you have been tasked to implement
a function that returns a list of all words from string s that contain exactly
n consonants, in order these words appear in the string s.
If the string s is empty then the function should return an empty list.
Note: you may assume the input string contains only letters and spaces.
Examples:
select_words("Mary had a little lamb", 4) ==> ["little"]
select_words("Mary had a little lamb", 3) ==> ["Mary", "lamb"]
select_words("simple white space", 2) ==> []
select_words("Hello world", 4) ==> ["world"]
select_words("Uncle sam", 3) ==> ["Uncle"] *)

Require Import Coq.Strings.Ascii Coq.Strings.String Coq.Lists.List Coq.Arith.Arith Coq.Bool.Bool.
Import ListNotations.



Definition is_vowel (c : ascii) : bool :=
  match c with
  | "a"%char => true | "e"%char => true | "i"%char => true | "o"%char => true | "u"%char => true
  | "A"%char => true | "E"%char => true | "I"%char => true | "O"%char => true | "U"%char => true
  | _ => false
  end.

Definition is_letter (c : ascii) : bool :=
  let n := nat_of_ascii c in
  ((Nat.leb 65 n) && (Nat.leb n 90)) ||
  ((Nat.leb 97 n) && (Nat.leb n 122)).

Definition is_consonant (c : ascii) : bool :=
  is_letter c && negb (is_vowel c).

Definition count_consonants (w : list ascii) : nat :=
  length (filter is_consonant w).

Definition only_spaces (xs : list ascii) : Prop :=
  Forall (fun c => c = " "%char) xs.

Definition nonempty_spaces (xs : list ascii) : Prop :=
  xs <> [] /\ only_spaces xs.

Definition word_chars (w : list ascii) : Prop :=
  w <> [] /\ Forall (fun c => c <> " "%char) w.

Definition separated_words
    (front : list (list ascii)) (seps : list (list ascii)) (last : list ascii)
    : list ascii :=
  (concat (map (fun ws => ((fst ws) ++ (snd ws))%list) (combine front seps)) ++ last)%list.

Definition split_words_shape (s : list ascii) (words : list (list ascii)) : Prop :=
  (words = [] /\ only_spaces s) \/
  exists leading trailing front last seps,
    words = (front ++ [last])%list /\
    Forall word_chars (front ++ [last]) /\
    only_spaces leading /\
    only_spaces trailing /\
    Forall nonempty_spaces seps /\
    length seps = length front /\
    s = (leading ++ separated_words front seps last ++ trailing)%list.

Definition select_words_impl (words : list (list ascii)) (n : nat) : list (list ascii) :=
  filter (fun w => Nat.eqb (count_consonants w) n) words.

(* 字符串只含字母与空格 *)
Definition problem_117_pre (s : string) : Prop :=
  let l := list_ascii_of_string s in
  Forall (fun c => c = " "%char \/ let n := nat_of_ascii c in (65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122)) l.

Definition problem_117_spec (s : string) (n : nat) (output : list string) : Prop :=
  exists words,
    split_words_shape (list_ascii_of_string s) words /\
    output = map string_of_list_ascii (select_words_impl words n).
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
Local Open Scope string_scope.
Local Open Scope list_scope.
Import naive_C_Rules.
Local Open Scope sac.

Definition ascii_of_z_117 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_117 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_117 c) (string_of_list_z_117 rest)
  end.

Definition row_payload_z_117 (row : list Z) : list Z :=
  firstn (Z.to_nat (Zlength row - 1)) row.

Definition row_string_z_117 (row : list Z) : string :=
  string_of_list_z_117 (row_payload_z_117 row).

Definition rows_to_strings_z_117 (rows : list (list Z)) : list string :=
  map row_string_z_117 rows.

Definition problem_117_pre_z (s : list Z) : Prop :=
  problem_117_pre (string_of_list_z_117 s).

Definition problem_117_spec_z (s : list Z) (need : Z) (rows : list (list Z)) : Prop :=
  problem_117_spec (string_of_list_z_117 s) (Z.to_nat need) (rows_to_strings_z_117 rows).

Definition is_space_z_117 (c : Z) : bool :=
  Z.eqb c 32.

Definition is_letter_z_117 (c : Z) : bool :=
  (Z.leb 65 c && Z.leb c 90) || (Z.leb 97 c && Z.leb c 122).

Definition is_vowel_z_117 (c : Z) : bool :=
  Z.eqb c 65 || Z.eqb c 69 || Z.eqb c 73 || Z.eqb c 79 || Z.eqb c 85 ||
  Z.eqb c 97 || Z.eqb c 101 || Z.eqb c 105 || Z.eqb c 111 || Z.eqb c 117.

Definition is_consonant_z_117 (c : Z) : bool :=
  is_letter_z_117 c && negb (is_vowel_z_117 c).

Fixpoint count_consonants_z_117 (w : list Z) : Z :=
  match w with
  | [] => 0
  | c :: rest =>
      (if is_consonant_z_117 c then 1 else 0) + count_consonants_z_117 rest
  end.

Definition valid_select_words_char_117 (c : Z) : Prop :=
  c = 32 \/ (65 <= c <= 90) \/ (97 <= c <= 122).

Definition valid_select_words_input_117 (s : list Z) : Prop :=
  forall i, 0 <= i < Zlength s -> valid_select_words_char_117 (Znth i s 0).

Definition word_payload_117 (s : list Z) (start stop : Z) : list Z :=
  sublist start stop s.

Definition word_row_117 (s : list Z) (start stop : Z) : list Z :=
  c_string (word_payload_117 s start stop).

Definition select_step_117
    (need : Z) (st : list (list Z) * list Z) (c : Z)
    : list (list Z) * list Z :=
  let '(rows, cur) := st in
  if is_space_z_117 c then
    match cur with
    | [] => (rows, [])
    | _ =>
        if Z.eqb (count_consonants_z_117 cur) need
        then (rows ++ [cur], [])
        else (rows, [])
    end
  else (rows, cur ++ [c]).

Fixpoint select_state_nat_117 (n : nat) (s : list Z) (need : Z)
  : list (list Z) * list Z :=
  match n with
  | O => ([], [])
  | S n' =>
      select_step_117 need
        (select_state_nat_117 n' s need)
        (Znth (Z.of_nat n') s 0)
  end.

Definition select_completed_payloads_117 (s : list Z) (i need : Z)
    : list (list Z) :=
  fst (select_state_nat_117 (Z.to_nat i) s need).

Definition select_current_117 (s : list Z) (i need : Z) : list Z :=
  snd (select_state_nat_117 (Z.to_nat i) s need).

Definition select_completed_rows_117 (s : list Z) (i need : Z)
    : list (list Z) :=
  map c_string (select_completed_payloads_117 s i need).

Definition select_payloads_117 (s : list Z) (need : Z) : list (list Z) :=
  let '(rows, cur) := select_state_nat_117 (Z.to_nat (Zlength s)) s need in
  match cur with
  | [] => rows
  | _ =>
      if Z.eqb (count_consonants_z_117 cur) need
      then rows ++ [cur]
      else rows
  end.

Definition all_step_117
    (st : list (list Z) * list Z) (c : Z)
    : list (list Z) * list Z :=
  let '(rows, cur) := st in
  if is_space_z_117 c then
    match cur with
    | [] => (rows, [])
    | _ => (rows ++ [cur], [])
    end
  else (rows, cur ++ [c]).

Fixpoint all_state_nat_117 (n : nat) (s : list Z)
  : list (list Z) * list Z :=
  match n with
  | O => ([], [])
  | S n' =>
      all_step_117
        (all_state_nat_117 n' s)
        (Znth (Z.of_nat n') s 0)
  end.

Definition all_payloads_117 (s : list Z) : list (list Z) :=
  let '(rows, cur) := all_state_nat_117 (Z.to_nat (Zlength s)) s in
  match cur with
  | [] => rows
  | _ => rows ++ [cur]
  end.

Definition only_spaces_z_117 (xs : list Z) : Prop :=
  Forall (fun c => c = 32) xs.

Definition nonempty_spaces_z_117 (xs : list Z) : Prop :=
  xs <> [] /\ only_spaces_z_117 xs.

Definition word_chars_z_117 (w : list Z) : Prop :=
  w <> [] /\ Forall (fun c => c <> 32) w.

Definition separated_words_z_117
    (front : list (list Z)) (seps : list (list Z)) (last : list Z)
    : list Z :=
  (List.concat (map (fun ws => (fst ws ++ snd ws)%list) (combine front seps)) ++ last)%list.

Definition split_words_shape_z_117 (s : list Z) (words : list (list Z)) : Prop :=
  (words = [] /\ only_spaces_z_117 s) \/
  exists leading trailing front last seps,
    words = (front ++ [last])%list /\
    Forall word_chars_z_117 (front ++ [last])%list /\
    only_spaces_z_117 leading /\
    only_spaces_z_117 trailing /\
    Forall nonempty_spaces_z_117 seps /\
    List.length seps = List.length front /\
    s = (leading ++ separated_words_z_117 front seps last ++ trailing)%list.

Definition closed_shape_z_117 (s : list Z) (rows : list (list Z)) : Prop :=
  (rows = [] /\ only_spaces_z_117 s) \/
  exists leading trailing front last seps,
    rows = (front ++ [last])%list /\
    Forall word_chars_z_117 (front ++ [last])%list /\
    only_spaces_z_117 leading /\
    nonempty_spaces_z_117 trailing /\
    Forall nonempty_spaces_z_117 seps /\
    List.length seps = List.length front /\
    s = (leading ++ separated_words_z_117 front seps last ++ trailing)%list.

Definition open_shape_z_117
    (s : list Z) (rows : list (list Z)) (cur : list Z) : Prop :=
  exists leading front seps,
    rows = front /\
    Forall word_chars_z_117 (front ++ [cur])%list /\
    only_spaces_z_117 leading /\
    Forall nonempty_spaces_z_117 seps /\
    List.length seps = List.length front /\
    s = (leading ++ separated_words_z_117 front seps cur)%list.

Definition state_shape_z_117
    (s : list Z) (rows : list (list Z)) (cur : list Z) : Prop :=
  match cur with
  | [] => closed_shape_z_117 s rows
  | _ => open_shape_z_117 s rows cur
  end.

Definition select_output_rows_117 (s : list Z) (need : Z) : list (list Z) :=
  map c_string (select_payloads_117 s need).

Definition select_scan_state_117
    (s : list Z) (i start numc need : Z) (rows : list (list Z)) : Prop :=
  0 <= i <= string_length s /\
  rows = select_completed_rows_117 s i need /\
  ((select_current_117 s i need = [] /\ start = -1 /\ numc = 0) \/
   (0 <= start < i /\
    select_current_117 s i need = word_payload_117 s start i /\
    numc = count_consonants_z_117 (word_payload_117 s start i))).

Fixpoint select_words_rows_heap_117
    (row_ptrs : list Z) (rows : list (list Z)) : Assertion :=
  match row_ptrs, rows with
  | p :: ps, row :: rs =>
      CharArray.full p (Zlength row) row ** select_words_rows_heap_117 ps rs
  | _, _ => emp
  end.

Lemma select_words_rows_heap_117_nil :
  emp |-- select_words_rows_heap_117 nil nil.
Proof.
  simpl.
  entailer!.
Qed.

Lemma select_words_rows_heap_117_app_single : forall ptrs rows p row,
  Zlength ptrs = Zlength rows ->
  select_words_rows_heap_117 ptrs rows ** CharArray.full p (Zlength row) row
  |-- select_words_rows_heap_117 (ptrs ++ [p]) (rows ++ [row]).
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

Lemma count_consonants_z_117_nonneg : forall w,
  0 <= count_consonants_z_117 w.
Proof.
  induction w as [| c rest IH]; simpl; [lia|].
  destruct (is_consonant_z_117 c); lia.
Qed.

Lemma count_consonants_z_117_app_single : forall w c,
  count_consonants_z_117 (w ++ [c]) =
  count_consonants_z_117 w + if is_consonant_z_117 c then 1 else 0.
Proof.
  induction w as [| x xs IH]; intros c; simpl.
  - destruct (is_consonant_z_117 c); lia.
  - rewrite IH.
    destruct (is_consonant_z_117 x);
      destruct (is_consonant_z_117 c); lia.
Qed.

Lemma select_state_nat_117_step : forall i s need,
  0 <= i ->
  select_state_nat_117 (Z.to_nat (i + 1)) s need =
  select_step_117 need (select_state_nat_117 (Z.to_nat i) s need) (Znth i s 0).
Proof.
  intros i s need Hi.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  reflexivity.
Qed.

Lemma select_scan_state_117_initial : forall s need,
  0 <= string_length s ->
  select_scan_state_117 s 0 (-1) 0 need [].
Proof.
  intros s need Hlen.
  unfold select_scan_state_117, select_completed_rows_117,
    select_completed_payloads_117, select_current_117.
  simpl.
  repeat split; try lia.
  left; repeat split; reflexivity.
Qed.

Lemma select_scan_state_117_current_nonempty : forall s i start numc need rows,
  select_scan_state_117 s i start numc need rows ->
  start >= 0 ->
  select_current_117 s i need = word_payload_117 s start i /\
  numc = count_consonants_z_117 (word_payload_117 s start i).
Proof.
  intros s i start numc need rows Hstate Hstart.
  unfold select_scan_state_117 in Hstate.
  destruct Hstate as [_ [_ [Hempty | Hcur]]].
  - destruct Hempty as [_ [Hstart_eq _]]; lia.
  - tauto.
Qed.

Lemma select_completed_rows_117_step_selected : forall s i need rows cur,
  0 <= i ->
  select_state_nat_117 (Z.to_nat i) s need = (rows, cur) ->
  is_space_z_117 (Znth i s 0) = true ->
  cur <> [] ->
  count_consonants_z_117 cur = need ->
  select_completed_rows_117 s (i + 1) need =
  map c_string rows ++ [c_string cur].
Proof.
  intros s i need rows cur Hi Hst Hspace Hcur Hcount.
  unfold select_completed_rows_117, select_completed_payloads_117.
  rewrite select_state_nat_117_step by lia.
  rewrite Hst.
  unfold select_step_117.
  rewrite Hspace.
  destruct cur; [contradiction|].
  rewrite Hcount, Z.eqb_refl.
  simpl.
  rewrite map_app.
  reflexivity.
Qed.

Lemma select_completed_rows_117_step_not_selected : forall s i need rows cur,
  0 <= i ->
  select_state_nat_117 (Z.to_nat i) s need = (rows, cur) ->
  is_space_z_117 (Znth i s 0) = true ->
  count_consonants_z_117 cur <> need ->
  select_completed_rows_117 s (i + 1) need = map c_string rows.
Proof.
  intros s i need rows cur Hi Hst Hspace Hcount.
  unfold select_completed_rows_117, select_completed_payloads_117.
  rewrite select_state_nat_117_step by lia.
  rewrite Hst.
  unfold select_step_117.
  rewrite Hspace.
  destruct cur as [| x xs]; [reflexivity|].
  destruct (Z.eqb_spec (count_consonants_z_117 (x :: xs)) need).
  - contradiction.
  - reflexivity.
Qed.

Lemma select_completed_rows_117_step_space_empty : forall s i need rows,
  0 <= i ->
  select_state_nat_117 (Z.to_nat i) s need = (rows, []) ->
  is_space_z_117 (Znth i s 0) = true ->
  select_completed_rows_117 s (i + 1) need = map c_string rows.
Proof.
  intros s i need rows Hi Hst Hspace.
  unfold select_completed_rows_117, select_completed_payloads_117.
  rewrite select_state_nat_117_step by lia.
  rewrite Hst.
  unfold select_step_117.
  rewrite Hspace.
  reflexivity.
Qed.

Lemma select_current_117_step_nospace : forall s i need rows cur,
  0 <= i ->
  select_state_nat_117 (Z.to_nat i) s need = (rows, cur) ->
  is_space_z_117 (Znth i s 0) = false ->
  select_current_117 s (i + 1) need = cur ++ [Znth i s 0].
Proof.
  intros s i need rows cur Hi Hst Hspace.
  unfold select_current_117.
  rewrite select_state_nat_117_step by lia.
  rewrite Hst.
  unfold select_step_117.
  rewrite Hspace.
  reflexivity.
Qed.

Lemma c_string_Znth_before_117 : forall s i,
  0 <= i < Zlength s ->
  Znth i (c_string s) 0 = Znth i s 0.
Proof.
  intros s i Hi.
  unfold c_string.
  rewrite app_Znth1 by lia.
  reflexivity.
Qed.

Lemma Zlength_word_payload_117 : forall s start stop,
  0 <= start <= stop ->
  stop <= Zlength s ->
  Zlength (word_payload_117 s start stop) = stop - start.
Proof.
  intros s start stop Hbounds Hstop.
  unfold word_payload_117.
  rewrite Zlength_sublist by lia.
  lia.
Qed.

Lemma word_payload_117_empty : forall s start,
  word_payload_117 s start start = [].
Proof.
  intros s start.
  unfold word_payload_117.
  apply sublist_nil.
  lia.
Qed.

Lemma word_payload_117_step : forall s start i,
  0 <= start /\ start <= i /\ i < Zlength s ->
  word_payload_117 s start (i + 1) =
  word_payload_117 s start i ++ [Znth i s 0].
Proof.
  intros s start i Hbounds.
  unfold word_payload_117.
  rewrite (sublist_split start (i + 1) i s) by lia.
  replace (sublist i (i + 1) s) with [Znth i s 0].
  - reflexivity.
  - symmetry.
    apply sublist_single.
    lia.
Qed.

Lemma word_payload_117_step_offset_c_string : forall s start k,
  0 <= start ->
  0 <= k ->
  start + k < Zlength s ->
  word_payload_117 s start (start + (k + 1)) =
  word_payload_117 s start (start + k) ++
    [Znth (start + k) (c_string s) 0].
Proof.
  intros s start k Hstart Hk Hlt.
  replace (start + (k + 1)) with ((start + k) + 1) by lia.
  rewrite word_payload_117_step by lia.
  rewrite c_string_Znth_before_117 by lia.
  reflexivity.
Qed.

Lemma word_row_117_unfold : forall s start stop,
  word_row_117 s start stop =
  word_payload_117 s start stop ++ [0].
Proof.
  intros.
  unfold word_row_117, c_string.
  reflexivity.
Qed.

Lemma is_space_z_117_true_32 : forall s i,
  0 <= i < Zlength s ->
  Znth i (c_string s) 0 = 32 ->
  is_space_z_117 (Znth i s 0) = true.
Proof.
  intros s i Hi H.
  unfold is_space_z_117.
  rewrite <- (c_string_Znth_before_117 s i) by lia.
  rewrite H.
  reflexivity.
Qed.

Lemma is_space_z_117_false_from_neq : forall s i,
  0 <= i < Zlength s ->
  Znth i (c_string s) 0 <> 32 ->
  is_space_z_117 (Znth i s 0) = false.
Proof.
  intros s i Hi H32.
  unfold is_space_z_117.
  rewrite <- (c_string_Znth_before_117 s i) by lia.
  destruct (Z.eqb_spec (Znth i (c_string s) 0) 32); [congruence|].
  reflexivity.
Qed.

Lemma select_completed_rows_117_step_nospace : forall s i need rows cur,
  0 <= i ->
  select_state_nat_117 (Z.to_nat i) s need = (rows, cur) ->
  is_space_z_117 (Znth i s 0) = false ->
  select_completed_rows_117 s (i + 1) need = map c_string rows.
Proof.
  intros s i need rows cur Hi Hst Hspace.
  unfold select_completed_rows_117, select_completed_payloads_117.
  rewrite select_state_nat_117_step by lia.
  rewrite Hst.
  unfold select_step_117.
  rewrite Hspace.
  reflexivity.
Qed.

Lemma select_scan_state_117_step_space_empty : forall s i need rows,
  0 <= i < string_length s ->
  select_scan_state_117 s i (-1) 0 need rows ->
  is_space_z_117 (Znth i s 0) = true ->
  select_scan_state_117 s (i + 1) (-1) 0 need rows.
Proof.
  intros s i need rows Hrange Hstate Hspace.
  unfold select_scan_state_117 in Hstate |- *.
  destruct Hstate as [_ [Hrows [Hempty | Hcur]]].
  - destruct Hempty as [Hcurrent [Hstart Hnumc]].
    destruct (select_state_nat_117 (Z.to_nat i) s need) as [payloads cur] eqn:Hst.
    unfold select_current_117 in Hcurrent.
    rewrite Hst in Hcurrent.
    simpl in Hcurrent.
    subst cur.
    assert (Hold : select_completed_rows_117 s i need = map c_string payloads)
      by (unfold select_completed_rows_117, select_completed_payloads_117;
          rewrite Hst; reflexivity).
    repeat split; try (unfold string_length, naive_C_Rules.string_length in *; lia).
    + rewrite Hrows, Hold.
      symmetry.
      apply select_completed_rows_117_step_space_empty with (rows := payloads);
        try assumption; lia.
    + left.
      repeat split; try reflexivity.
      unfold select_current_117.
      rewrite select_state_nat_117_step by lia.
      rewrite Hst.
      unfold select_step_117.
      rewrite Hspace.
      reflexivity.
  - destruct Hcur as [Hstart _].
    lia.
Qed.

Lemma select_scan_state_117_step_space_not_selected : forall s i start numc need rows,
  0 <= i < string_length s ->
  select_scan_state_117 s i start numc need rows ->
  0 <= start ->
  is_space_z_117 (Znth i s 0) = true ->
  numc <> need ->
  select_scan_state_117 s (i + 1) (-1) 0 need rows.
Proof.
  intros s i start numc need rows Hrange Hstate Hstart Hspace Hneq.
  unfold select_scan_state_117 in Hstate |- *.
  destruct Hstate as [_ [Hrows [Hempty | Hcur]]].
  - destruct Hempty as [_ [Hstart_eq _]].
    lia.
  - destruct Hcur as [Hstart_bounds [Hcurrent Hnumc]].
    destruct (select_state_nat_117 (Z.to_nat i) s need) as [payloads cur] eqn:Hst.
    unfold select_current_117 in Hcurrent.
    rewrite Hst in Hcurrent.
    simpl in Hcurrent.
    subst cur.
    assert (Hold : select_completed_rows_117 s i need = map c_string payloads)
      by (unfold select_completed_rows_117, select_completed_payloads_117;
          rewrite Hst; reflexivity).
    repeat split; try (unfold string_length, naive_C_Rules.string_length in *; lia).
    + rewrite Hrows, Hold.
      symmetry.
      apply select_completed_rows_117_step_not_selected with
        (cur := word_payload_117 s start i); try assumption; try lia.
    + left.
      repeat split; try reflexivity.
      unfold select_current_117.
      rewrite select_state_nat_117_step by lia.
      rewrite Hst.
      unfold select_step_117.
      rewrite Hspace.
      destruct (word_payload_117 s start i) as [| c cs] eqn:Hpayload.
      * apply (f_equal (@Zlength Z)) in Hpayload.
        rewrite Zlength_word_payload_117 in Hpayload by (unfold string_length, naive_C_Rules.string_length in *; lia).
        rewrite Zlength_nil in Hpayload.
        lia.
      * rewrite <- Hnumc.
        destruct (Z.eqb_spec numc need); [contradiction|reflexivity].
Qed.

Lemma select_scan_state_117_step_space_selected : forall s i start numc need rows,
  0 <= i < string_length s ->
  select_scan_state_117 s i start numc need rows ->
  0 <= start ->
  is_space_z_117 (Znth i s 0) = true ->
  numc = need ->
  select_scan_state_117 s (i + 1) (-1) 0 need (rows ++ [word_row_117 s start i]).
Proof.
  intros s i start numc need rows Hrange Hstate Hstart Hspace Heq.
  unfold select_scan_state_117 in Hstate |- *.
  destruct Hstate as [_ [Hrows [Hempty | Hcur]]].
  - destruct Hempty as [_ [Hstart_eq _]].
    lia.
  - destruct Hcur as [Hstart_bounds [Hcurrent Hnumc]].
    destruct (select_state_nat_117 (Z.to_nat i) s need) as [payloads cur] eqn:Hst.
    unfold select_current_117 in Hcurrent.
    rewrite Hst in Hcurrent.
    simpl in Hcurrent.
    subst cur.
    assert (Hold : select_completed_rows_117 s i need = map c_string payloads)
      by (unfold select_completed_rows_117, select_completed_payloads_117;
          rewrite Hst; reflexivity).
    repeat split; try lia.
    + rewrite Hrows, Hold.
      unfold word_row_117.
      symmetry.
      apply select_completed_rows_117_step_selected with
        (cur := word_payload_117 s start i); try assumption; try lia.
      {
        intro Hnil.
        apply (f_equal (@Zlength Z)) in Hnil.
        rewrite Zlength_word_payload_117 in Hnil by (unfold string_length, naive_C_Rules.string_length in *; lia).
        rewrite Zlength_nil in Hnil.
        lia.
      }
    + left.
      repeat split; try reflexivity.
      unfold select_current_117.
      rewrite select_state_nat_117_step by lia.
      rewrite Hst.
      unfold select_step_117.
      rewrite Hspace.
      destruct (word_payload_117 s start i) as [| c cs] eqn:Hpayload.
      * apply (f_equal (@Zlength Z)) in Hpayload.
        rewrite Zlength_word_payload_117 in Hpayload by (unfold string_length, naive_C_Rules.string_length in *; lia).
        rewrite Zlength_nil in Hpayload.
        lia.
      * rewrite <- Hnumc.
        rewrite Heq, Z.eqb_refl.
        reflexivity.
Qed.

Lemma select_scan_state_117_step_nospace : forall s i start numc need rows,
  0 <= i < string_length s ->
  select_scan_state_117 s i start numc need rows ->
  is_space_z_117 (Znth i s 0) = false ->
  select_scan_state_117 s (i + 1)
    (if Z.ltb start 0 then i else start)
    (numc + if is_consonant_z_117 (Znth i s 0) then 1 else 0)
    need rows.
Proof.
  intros s i start numc need rows Hrange Hstate Hspace.
  unfold select_scan_state_117 in Hstate |- *.
  destruct Hstate as [_ [Hrows [Hempty | Hcur]]].
  - destruct Hempty as [Hcurrent [Hstart Hnumc]].
    destruct (select_state_nat_117 (Z.to_nat i) s need) as [payloads cur] eqn:Hst.
    unfold select_current_117 in Hcurrent.
    rewrite Hst in Hcurrent.
    simpl in Hcurrent.
    subst cur start numc.
    assert (Hold : select_completed_rows_117 s i need = map c_string payloads)
      by (unfold select_completed_rows_117, select_completed_payloads_117;
          rewrite Hst; reflexivity).
    repeat split; try lia.
    + rewrite Hrows, Hold.
      symmetry.
      apply select_completed_rows_117_step_nospace with (cur := []);
        try assumption; unfold string_length, naive_C_Rules.string_length in *; lia.
    + right.
      change ((-1 <? 0)%Z) with true.
      repeat split; try (unfold string_length, naive_C_Rules.string_length in *; lia).
      * unfold select_current_117.
        change (Z.to_nat (Z.succ i)) with (Z.to_nat (i + 1)).
        rewrite select_state_nat_117_step by lia.
        rewrite Hst.
        unfold select_step_117.
        rewrite Hspace.
        simpl.
        unfold word_payload_117.
        rewrite (@sublist_single Z 0 i s) by (unfold string_length, naive_C_Rules.string_length in *; lia).
        reflexivity.
      * unfold word_payload_117.
        rewrite (@sublist_single Z 0 i s) by (unfold string_length, naive_C_Rules.string_length in *; lia).
        simpl.
        destruct (is_consonant_z_117 (Znth i s 0)); lia.
  - destruct Hcur as [Hstart_bounds [Hcurrent Hnumc]].
    destruct (select_state_nat_117 (Z.to_nat i) s need) as [payloads cur] eqn:Hst.
    unfold select_current_117 in Hcurrent.
    rewrite Hst in Hcurrent.
    simpl in Hcurrent.
    subst cur.
    assert (Hold : select_completed_rows_117 s i need = map c_string payloads)
      by (unfold select_completed_rows_117, select_completed_payloads_117;
          rewrite Hst; reflexivity).
    repeat split; try (unfold string_length, naive_C_Rules.string_length in *; lia).
    + rewrite Hrows, Hold.
      symmetry.
      apply select_completed_rows_117_step_nospace with
        (cur := word_payload_117 s start i); try assumption;
        unfold string_length, naive_C_Rules.string_length in *; lia.
    + right.
      destruct (Z.ltb_spec start 0); [lia|].
      repeat split; try (unfold string_length, naive_C_Rules.string_length in *; lia).
      * unfold select_current_117.
        change (Z.to_nat (Z.succ i)) with (Z.to_nat (i + 1)).
        rewrite select_state_nat_117_step by lia.
        rewrite Hst.
        unfold select_step_117.
        rewrite Hspace.
        rewrite word_payload_117_step by (unfold string_length, naive_C_Rules.string_length in *; lia).
        reflexivity.
      * rewrite word_payload_117_step by (unfold string_length, naive_C_Rules.string_length in *; lia).
        rewrite count_consonants_z_117_app_single.
        rewrite <- Hnumc.
        lia.
Qed.

Lemma select_scan_state_117_final_empty : forall s need rows,
  select_scan_state_117 s (string_length s) (-1) 0 need rows ->
  rows = select_output_rows_117 s need.
Proof.
  intros s need rows Hstate.
  unfold select_scan_state_117 in Hstate.
  destruct Hstate as [_ [Hrows [Hempty | Hcur]]].
  - destruct Hempty as [Hcurrent [_ _]].
    unfold string_length, naive_C_Rules.string_length in *.
    unfold select_output_rows_117, select_payloads_117.
    unfold select_current_117 in Hcurrent.
    unfold select_completed_rows_117, select_completed_payloads_117 in Hrows.
    destruct (select_state_nat_117 (Z.to_nat (Zlength s)) s need)
      as [payloads cur] eqn:Hst.
    simpl in Hcurrent, Hrows.
    subst cur rows.
    reflexivity.
  - destruct Hcur as [Hstart _].
    pose proof (string_length_nonneg s).
    lia.
Qed.

Lemma select_scan_state_117_final_not_selected : forall s start numc need rows,
  select_scan_state_117 s (string_length s) start numc need rows ->
  0 <= start ->
  numc <> need ->
  rows = select_output_rows_117 s need.
Proof.
  intros s start numc need rows Hstate Hstart Hneq.
  unfold select_scan_state_117 in Hstate.
  destruct Hstate as [_ [Hrows [Hempty | Hcur]]].
  - destruct Hempty as [_ [Hstart_eq _]].
    lia.
  - destruct Hcur as [Hstart_bounds [Hcurrent Hnumc]].
    unfold string_length, naive_C_Rules.string_length in *.
    unfold select_output_rows_117, select_payloads_117.
    unfold select_current_117 in Hcurrent.
    unfold select_completed_rows_117, select_completed_payloads_117 in Hrows.
    destruct (select_state_nat_117 (Z.to_nat (Zlength s)) s need)
      as [payloads cur] eqn:Hst.
    simpl in Hcurrent, Hrows.
    subst cur rows.
    destruct (word_payload_117 s start (Zlength s)) as [| c cs].
    + reflexivity.
    + rewrite <- Hnumc.
      destruct (Z.eqb_spec numc need); [contradiction|reflexivity].
Qed.

Lemma select_scan_state_117_final_selected : forall s start numc need rows,
  select_scan_state_117 s (string_length s) start numc need rows ->
  0 <= start ->
  numc = need ->
  rows ++ [word_row_117 s start (string_length s)] = select_output_rows_117 s need.
Proof.
  intros s start numc need rows Hstate Hstart Heq.
  unfold select_scan_state_117 in Hstate.
  destruct Hstate as [_ [Hrows [Hempty | Hcur]]].
  - destruct Hempty as [_ [Hstart_eq _]].
    lia.
  - destruct Hcur as [Hstart_bounds [Hcurrent Hnumc]].
    unfold string_length, naive_C_Rules.string_length in *.
    unfold select_output_rows_117, select_payloads_117.
    unfold select_current_117 in Hcurrent.
    unfold select_completed_rows_117, select_completed_payloads_117 in Hrows.
    destruct (select_state_nat_117 (Z.to_nat (Zlength s)) s need)
      as [payloads cur] eqn:Hst.
    simpl in Hcurrent, Hrows.
    subst cur rows.
    unfold word_row_117.
    change [c_string (word_payload_117 s start (Zlength s))]
      with (map c_string [word_payload_117 s start (Zlength s)]).
    rewrite <- map_app.
    destruct (word_payload_117 s start (Zlength s)) as [| c cs] eqn:Hpayload.
    + apply (f_equal (@Zlength Z)) in Hpayload.
      rewrite Zlength_word_payload_117 in Hpayload by (unfold string_length, naive_C_Rules.string_length in *; lia).
      rewrite Zlength_nil in Hpayload.
      lia.
    + rewrite <- Hnumc.
      rewrite Heq, Z.eqb_refl.
      reflexivity.
Qed.

Lemma Zlength_map_117 : forall {A B : Type} (f : A -> B) (l : list A),
  Zlength (map f l) = Zlength l.
Proof.
  intros.
  repeat rewrite Zlength_correct.
  rewrite length_map.
  reflexivity.
Qed.

Lemma select_state_nat_117_rows_bound : forall n s need rows cur,
  select_state_nat_117 n s need = (rows, cur) ->
  Zlength rows <= Z.of_nat n.
Proof.
  induction n as [| n IH]; intros s need rows cur Hst; simpl in Hst.
  - inversion Hst; subst. rewrite Zlength_nil. lia.
  - destruct (select_state_nat_117 n s need) as [rows0 cur0] eqn:Hprev.
    unfold select_step_117 in Hst.
    destruct (is_space_z_117 (Znth (Z.of_nat n) s 0)).
    + destruct cur0 as [| c cs].
      * inversion Hst; subst.
        specialize (IH s need rows [] Hprev). lia.
      * destruct (Z.eqb (count_consonants_z_117 (c :: cs)) need);
          inversion Hst; subst.
        -- rewrite Zlength_app, Zlength_cons, Zlength_nil.
           specialize (IH s need rows0 (c :: cs) Hprev). lia.
        -- specialize (IH s need rows (c :: cs) Hprev). lia.
    + inversion Hst; subst.
      specialize (IH s need rows cur0 Hprev). lia.
Qed.

Lemma Zlength_select_output_rows_117_le : forall s need,
  Zlength (select_output_rows_117 s need) <= Zlength s + 1.
Proof.
  intros s need.
  unfold select_output_rows_117, select_payloads_117.
  destruct (select_state_nat_117 (Z.to_nat (Zlength s)) s need) as [rows cur] eqn:Hst.
  destruct cur as [| c cs].
  - rewrite Zlength_map_117.
    pose proof (select_state_nat_117_rows_bound _ _ _ _ _ Hst).
    rewrite Z2Nat.id in H by (pose proof (Zlength_nonneg s); lia).
    lia.
  - destruct (Z.eqb (count_consonants_z_117 (c :: cs)) need).
    + rewrite Zlength_map_117, Zlength_app, Zlength_cons, Zlength_nil.
      pose proof (select_state_nat_117_rows_bound _ _ _ _ _ Hst).
      rewrite Z2Nat.id in H by (pose proof (Zlength_nonneg s); lia).
      lia.
    + rewrite Zlength_map_117.
      pose proof (select_state_nat_117_rows_bound _ _ _ _ _ Hst).
      rewrite Z2Nat.id in H by (pose proof (Zlength_nonneg s); lia).
      lia.
Qed.

Lemma select_state_nat_117_filter_all : forall n s need rows cur,
  all_state_nat_117 n s = (rows, cur) ->
  select_state_nat_117 n s need =
    (filter (fun w => Z.eqb (count_consonants_z_117 w) need) rows, cur).
Proof.
  induction n as [| n IH]; intros s need rows cur Hall; simpl in *.
  - inversion Hall; reflexivity.
  - destruct (all_state_nat_117 n s) as [rows0 cur0] eqn:Hall0.
    specialize (IH s need rows0 cur0 Hall0).
    unfold all_step_117 in Hall.
    unfold select_step_117.
    rewrite IH.
    destruct (is_space_z_117 (Znth (Z.of_nat n) s 0)).
    + destruct cur0 as [| c cs].
      * inversion Hall; reflexivity.
      * destruct (Z.eqb (count_consonants_z_117 (c :: cs)) need) eqn:Hcount;
          simpl in Hcount;
          inversion Hall; subst; simpl; rewrite filter_app; simpl; try rewrite Hcount;
          try rewrite app_nil_r;
          reflexivity.
    + inversion Hall; subst.
      reflexivity.
Qed.

Lemma select_payloads_117_filter_all : forall s need,
  select_payloads_117 s need =
  filter (fun w => Z.eqb (count_consonants_z_117 w) need)
    (all_payloads_117 s).
Proof.
  intros s need.
  unfold select_payloads_117, all_payloads_117.
  destruct (all_state_nat_117 (Z.to_nat (Zlength s)) s) as [rows cur] eqn:Hall.
  rewrite (select_state_nat_117_filter_all _ _ _ _ _ Hall).
  simpl.
  destruct cur as [| c cs].
  - reflexivity.
  - destruct (Z.eqb (count_consonants_z_117 (c :: cs)) need) eqn:Hcount;
      simpl in Hcount;
      rewrite filter_app; simpl; try rewrite Hcount; try rewrite app_nil_r; reflexivity.
Qed.

Lemma row_payload_c_string_117 : forall payload,
  row_payload_z_117 (c_string payload) = payload.
Proof.
  intros payload.
  unfold row_payload_z_117, c_string.
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

Lemma rows_to_strings_c_string_117 : forall payloads,
  rows_to_strings_z_117 (map c_string payloads) =
  map string_of_list_z_117 payloads.
Proof.
  induction payloads as [| p ps IH]; simpl; [reflexivity|].
  unfold row_string_z_117.
  rewrite row_payload_c_string_117.
  rewrite IH.
  reflexivity.
Qed.

Lemma string_of_list_ascii_map_ascii_of_z_117 : forall s,
  string_of_list_ascii (map ascii_of_z_117 s) = string_of_list_z_117 s.
Proof.
  induction s as [| x xs IH]; simpl; congruence.
Qed.

Lemma list_ascii_of_string_string_of_list_z_117 : forall s,
  list_ascii_of_string (string_of_list_z_117 s) =
  map ascii_of_z_117 s.
Proof.
  induction s as [| x xs IH]; simpl; congruence.
Qed.

Lemma nat_of_ascii_of_z_117 : forall z,
  0 <= z <= 127 ->
  nat_of_ascii (ascii_of_z_117 z) = Z.to_nat z.
Proof.
  intros z Hz.
  unfold ascii_of_z_117.
  rewrite nat_ascii_embedding by lia.
  reflexivity.
Qed.

Lemma ascii_of_z_117_eq_char : forall z n c,
  0 <= z <= 127 ->
  nat_of_ascii c = n ->
  ascii_of_z_117 z = c <-> z = Z.of_nat n.
Proof.
  intros z n c Hz Hc.
  split; intro H.
  - apply (f_equal nat_of_ascii) in H.
    rewrite nat_of_ascii_of_z_117 in H by lia.
    rewrite Hc in H.
    lia.
  - subst z.
    unfold ascii_of_z_117.
    rewrite Nat2Z.id.
    rewrite <- Hc.
    apply ascii_nat_embedding.
Qed.

Lemma ascii_of_z_117_space : ascii_of_z_117 32 = " "%char.
Proof.
  unfold ascii_of_z_117.
  reflexivity.
Qed.

Lemma is_space_ascii_z_117 : forall z,
  0 <= z <= 127 ->
  ascii_of_z_117 z = " "%char <-> z = 32.
Proof.
  intros z Hz.
  split; intro H.
  - apply (proj1 (ascii_of_z_117_eq_char z 32 " "%char Hz eq_refl)) in H.
    lia.
  - subst z.
    apply ascii_of_z_117_space.
Qed.

Lemma is_vowel_ascii_z_117 : forall z,
  0 <= z <= 127 ->
  is_vowel (ascii_of_z_117 z) = is_vowel_z_117 z.
Proof.
  intros z Hz.
  replace z with (Z.of_nat (Z.to_nat z)) by lia.
  remember (Z.to_nat z) as n.
  assert (Hn : (n <= 127)%nat) by lia.
  clear Hz Heqn z.
  do 128 (destruct n as [| n]; [vm_compute; reflexivity |]).
  lia.
Qed.

Lemma is_letter_ascii_z_117 : forall z,
  0 <= z <= 127 ->
  is_letter (ascii_of_z_117 z) = is_letter_z_117 z.
Proof.
  intros z Hz.
  replace z with (Z.of_nat (Z.to_nat z)) by lia.
  remember (Z.to_nat z) as n.
  assert (Hn : (n <= 127)%nat) by lia.
  clear Hz Heqn z.
  do 128 (destruct n as [| n]; [vm_compute; reflexivity |]).
  lia.
Qed.

Lemma is_consonant_ascii_z_117 : forall z,
  0 <= z <= 127 ->
  is_consonant (ascii_of_z_117 z) = is_consonant_z_117 z.
Proof.
  intros z Hz.
  unfold is_consonant, is_consonant_z_117.
  rewrite is_letter_ascii_z_117 by lia.
  rewrite is_vowel_ascii_z_117 by lia.
  reflexivity.
Qed.

Lemma only_spaces_z_117_app_space : forall xs,
  only_spaces_z_117 xs ->
  only_spaces_z_117 (xs ++ [32])%list.
Proof.
  intros xs H.
  unfold only_spaces_z_117 in *.
  apply Forall_app.
  split; [assumption|constructor; [reflexivity|constructor]].
Qed.

Lemma nonempty_spaces_z_117_app_space : forall xs,
  nonempty_spaces_z_117 xs ->
  nonempty_spaces_z_117 (xs ++ [32])%list.
Proof.
  intros xs [Hne Hsp].
  split.
  - intro Hnil.
    apply app_eq_nil in Hnil as [_ Hbad].
    discriminate.
  - apply only_spaces_z_117_app_space; assumption.
Qed.

Lemma word_chars_z_117_single : forall c,
  c <> 32 ->
  word_chars_z_117 [c].
Proof.
  intros c Hc.
  split; [discriminate|constructor; [assumption|constructor]].
Qed.

Lemma word_chars_z_117_app_char : forall w c,
  word_chars_z_117 w ->
  c <> 32 ->
  word_chars_z_117 (w ++ [c])%list.
Proof.
  intros w c [Hne Hall] Hc.
  split.
  - intro Hnil.
    apply app_eq_nil in Hnil as [Hw _].
    contradiction.
  - apply Forall_app.
    split; [assumption|constructor; [assumption|constructor]].
Qed.

Lemma separated_words_z_117_app_single : forall front seps last sep cur,
  List.length seps = List.length front ->
  separated_words_z_117 (front ++ [last])%list (seps ++ [sep])%list cur =
  (separated_words_z_117 front seps last ++ sep ++ cur)%list.
Proof.
  induction front as [| f front IH]; intros seps last sep cur Hlen;
    destruct seps as [| sp seps]; simpl in *; try discriminate.
  - unfold separated_words_z_117.
    simpl.
    rewrite app_nil_r.
    repeat rewrite app_assoc.
    reflexivity.
  - inversion Hlen.
    unfold separated_words_z_117.
    simpl.
    rewrite <- app_assoc.
    fold (separated_words_z_117 (front ++ [last])%list (seps ++ [sep])%list cur).
    rewrite IH by assumption.
    change (separated_words_z_117 front seps last) with
      (List.concat (map (fun ws : list Z * list Z => (fst ws ++ snd ws)%list)
        (combine front seps)) ++ last)%list.
    repeat rewrite app_assoc.
    reflexivity.
Qed.

Lemma separated_words_z_117_last_app : forall front seps cur c,
  separated_words_z_117 front seps (cur ++ [c])%list =
  (separated_words_z_117 front seps cur ++ [c])%list.
Proof.
  intros.
  unfold separated_words_z_117.
  rewrite app_assoc.
  reflexivity.
Qed.

Lemma all_state_nat_117_prefix_app : forall n s tail,
  Z.of_nat n <= Zlength s ->
  all_state_nat_117 n (s ++ tail)%list = all_state_nat_117 n s.
Proof.
  induction n as [| n IH]; intros s tail Hn; simpl; [reflexivity|].
  rewrite IH by lia.
  replace (Znth (Z.of_nat n) (s ++ tail) 0) with
    (Znth (Z.of_nat n) s 0).
  - reflexivity.
  - rewrite app_Znth1 by lia.
    reflexivity.
Qed.

Lemma all_state_nat_117_snoc : forall s c,
  all_state_nat_117 (Z.to_nat (Zlength (s ++ [c])%list)) (s ++ [c])%list =
  all_step_117 (all_state_nat_117 (Z.to_nat (Zlength s)) s) c.
Proof.
  intros s c.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  assert (Hzlen : Z.to_nat (Zlength s + Z.succ 0) = S (Z.to_nat (Zlength s)))
    by (pose proof (Zlength_nonneg s); lia).
  rewrite Hzlen.
  simpl.
  assert (Hprefix :
    all_state_nat_117 (Z.to_nat (Zlength s)) (s +:: c) =
    all_state_nat_117 (Z.to_nat (Zlength s)) s).
  {
    change (s +:: c) with (s ++ [c])%list.
    apply all_state_nat_117_prefix_app.
    pose proof (Zlength_nonneg s); lia.
  }
  rewrite Hprefix.
  replace (Z.of_nat (Z.to_nat (Zlength s))) with (Zlength s)
    by (pose proof (Zlength_nonneg s); lia).
  rewrite app_Znth2 by lia.
  replace (Zlength s - Zlength s) with 0 by lia.
  simpl.
  reflexivity.
Qed.

Lemma state_shape_z_117_step : forall s rows cur c,
  state_shape_z_117 s rows cur ->
  state_shape_z_117 (s ++ [c])%list
    (fst (all_step_117 (rows, cur) c))
    (snd (all_step_117 (rows, cur) c)).
Proof.
  intros s rows cur c Hshape.
  unfold all_step_117.
  destruct (is_space_z_117 c) eqn:Hspace.
  - apply Z.eqb_eq in Hspace.
    subst c.
    destruct cur as [| x xs].
    + simpl.
      unfold state_shape_z_117 in Hshape |- *.
      destruct Hshape as [[Hrows Hsp] | Hclosed].
      * left.
        split; [assumption|].
        apply only_spaces_z_117_app_space; assumption.
      * right.
        destruct Hclosed as [leading [trailing [front [last [seps Hclosed]]]]].
        destruct Hclosed as [Hrows [Hwords [Hlead [Htrail [Hseps [Hlen Heq]]]]]].
        exists leading, (trailing ++ [32]), front, last, seps.
        repeat split; try assumption.
        -- apply nonempty_spaces_z_117_app_space; assumption.
        -- apply only_spaces_z_117_app_space.
           destruct Htrail; assumption.
        -- change (s +:: 32) with (s ++ [32])%list.
           rewrite Heq.
           repeat rewrite app_assoc.
           reflexivity.
    + simpl.
      unfold state_shape_z_117 in Hshape.
      destruct Hshape as [leading [front [seps Hopen]]].
      destruct Hopen as [Hrows [Hwords [Hlead [Hseps [Hlen Heq]]]]].
      subst rows.
      right.
      exists leading, [32], front, (x :: xs), seps.
      repeat split; try assumption.
      * discriminate.
      * constructor; [reflexivity|constructor].
      * rewrite Heq.
        repeat rewrite app_assoc.
        reflexivity.
  - apply Z.eqb_neq in Hspace.
    destruct cur as [| x xs].
    + simpl.
      unfold state_shape_z_117 in Hshape |- *.
      destruct Hshape as [[Hrows Hsp] | Hclosed].
      * subst rows.
        exists s, [], [].
        repeat split; try assumption; simpl; try reflexivity.
        -- constructor; [apply word_chars_z_117_single; assumption|constructor].
        -- constructor.
      *
        destruct Hclosed as [leading [trailing [front [last [seps Hclosed]]]]].
        destruct Hclosed as [Hrows [Hwords [Hlead [Htrail [Hseps [Hlen Heq]]]]]].
        subst rows.
        exists leading, (front ++ [last]), (seps ++ [trailing]).
        repeat split.
        -- change ((front +:: last) +:: [c]) with
             ((front ++ [last]) ++ [[c]])%list.
           apply Forall_app.
           split; [assumption|constructor; [apply word_chars_z_117_single; assumption|constructor]].
        -- assumption.
        -- apply Forall_app.
           split; [assumption|constructor; [assumption|constructor]].
        -- change (List.length (seps +:: trailing) = List.length (front +:: last)).
           rewrite !app_length, Hlen; simpl; lia.
        -- rewrite separated_words_z_117_app_single by assumption.
           rewrite Heq.
           repeat rewrite app_assoc.
           reflexivity.
    + simpl.
      unfold state_shape_z_117 in Hshape |- *.
      destruct Hshape as [leading [front [seps Hopen]]].
      destruct Hopen as [Hrows [Hwords [Hlead [Hseps [Hlen Heq]]]]].
      exists leading, front, seps.
      repeat split; try assumption.
      * change (Forall word_chars_z_117 (front ++ [(x :: xs)])%list) in Hwords.
        change (Forall word_chars_z_117 (front ++ [(x :: xs) ++ [c]])%list).
        apply Forall_app.
        apply Forall_app in Hwords as [Hfront Hcur].
        split; [assumption|].
        inversion Hcur as [| ? ? Hcur_word _]; subst.
        constructor; [apply word_chars_z_117_app_char; assumption|constructor].
      * change (s +:: c) with (s ++ [c])%list.
        rewrite Heq.
        change (separated_words_z_117 front seps (x :: xs +:: c)) with
          (separated_words_z_117 front seps ((x :: xs) ++ [c])%list).
        rewrite separated_words_z_117_last_app.
        repeat rewrite app_assoc.
        reflexivity.
Qed.

Lemma all_state_nat_117_shape : forall s rows cur,
  all_state_nat_117 (Z.to_nat (Zlength s)) s = (rows, cur) ->
  state_shape_z_117 s rows cur.
Proof.
  apply (rev_ind (fun s =>
    forall rows cur,
      all_state_nat_117 (Z.to_nat (Zlength s)) s = (rows, cur) ->
      state_shape_z_117 s rows cur)); intros.
  - simpl in H.
    inversion H; subst.
    unfold state_shape_z_117, closed_shape_z_117, only_spaces_z_117.
    left; split; [reflexivity|constructor].
  - replace (all_state_nat_117 (Z.to_nat (Zlength (l ++ [x])%list)) (l ++ [x])%list)
      with (all_step_117 (all_state_nat_117 (Z.to_nat (Zlength l)) l) x) in H0
      by (symmetry; apply all_state_nat_117_snoc).
    destruct (all_state_nat_117 (Z.to_nat (Zlength l)) l) as [rows0 cur0] eqn:Hprev.
    specialize (H rows0 cur0 eq_refl).
    pose proof (state_shape_z_117_step l rows0 cur0 x H) as Hstep.
    destruct (all_step_117 (rows0, cur0) x) as [rows1 cur1] eqn:Hstep_eq.
    simpl in H0, Hstep.
    inversion H0; subst.
    exact Hstep.
Qed.

Lemma all_payloads_117_shape_z : forall s,
  split_words_shape_z_117 s (all_payloads_117 s).
Proof.
  intros s.
  unfold all_payloads_117.
  destruct (all_state_nat_117 (Z.to_nat (Zlength s)) s) as [rows cur] eqn:Hst.
  pose proof (all_state_nat_117_shape s rows cur Hst) as Hshape.
  destruct cur as [| c cs].
  - unfold state_shape_z_117 in Hshape.
    destruct Hshape as [[Hrows Hsp] | Hclosed].
    + left; split; assumption.
    + right.
      destruct Hclosed as [leading [trailing [front [last [seps Hclosed]]]]].
      destruct Hclosed as
        [Hrows [Hwords [Hlead [[Htrail_ne Htrail] [Hseps [Hlen Heq]]]]]].
      exists leading, trailing, front, last, seps.
      repeat split; try assumption.
  - unfold state_shape_z_117 in Hshape.
    destruct Hshape as [leading [front [seps Hopen]]].
    destruct Hopen as [Hrows [Hwords [Hlead [Hseps [Hlen Heq]]]]].
    subst rows.
    right.
    exists leading, (@nil Z), front, (c :: cs), seps.
    repeat split; try assumption.
    constructor.
    rewrite Heq.
    rewrite app_nil_r.
    reflexivity.
Qed.

Definition ascii_range_z_117 (z : Z) : Prop := 0 <= z <= 127.

Definition ascii_range_list_117 (xs : list Z) : Prop :=
  Forall ascii_range_z_117 xs.

Lemma all_ascii_Znth_nat_117 : forall s n,
  all_ascii s ->
  (n < List.length s)%nat ->
  ascii_range_z_117 (Znth (Z.of_nat n) s 0).
Proof.
  intros s n Hall Hn.
  apply Hall.
  rewrite Zlength_correct.
  lia.
Qed.

Lemma all_state_nat_117_range : forall n s rows cur,
  all_ascii s ->
  (n <= List.length s)%nat ->
  all_state_nat_117 n s = (rows, cur) ->
  Forall ascii_range_list_117 rows /\ ascii_range_list_117 cur.
Proof.
  induction n as [| n IH]; intros s rows cur Hall Hle Hst; simpl in Hst.
  - inversion Hst; subst.
    split; constructor.
  - destruct (all_state_nat_117 n s) as [rows0 cur0] eqn:Hprev.
    specialize (IH s rows0 cur0 Hall ltac:(lia) Hprev) as [Hrows Hcur].
    unfold all_step_117 in Hst.
    pose proof (all_ascii_Znth_nat_117 s n Hall ltac:(lia)) as Hchar.
    destruct (is_space_z_117 (Znth (Z.of_nat n) s 0)).
    + destruct cur0 as [| c cs].
      * inversion Hst; subst.
        split; assumption.
      * inversion Hst; subst.
        split.
        -- apply Forall_app.
           split; [assumption|constructor; [assumption|constructor]].
        -- constructor.
    + inversion Hst; subst.
      split; [assumption|].
      apply Forall_app.
      split; [assumption|constructor; [assumption|constructor]].
Qed.

Lemma all_payloads_117_range : forall s,
  all_ascii s ->
  Forall ascii_range_list_117 (all_payloads_117 s).
Proof.
  intros s Hall.
  unfold all_payloads_117.
  destruct (all_state_nat_117 (Z.to_nat (Zlength s)) s) as [rows cur] eqn:Hst.
  pose proof (all_state_nat_117_range (Z.to_nat (Zlength s)) s rows cur Hall ltac:(
    rewrite Zlength_correct; lia) Hst) as [Hrows Hcur].
  destruct cur as [| c cs].
  - assumption.
  - apply Forall_app.
    split; [assumption|constructor; [assumption|constructor]].
Qed.

Lemma only_spaces_z_ascii_117 : forall xs,
  only_spaces_z_117 xs ->
  only_spaces (map ascii_of_z_117 xs).
Proof.
  intros xs H.
  induction H; simpl; constructor; auto.
  subst x.
  apply ascii_of_z_117_space.
Qed.

Lemma word_chars_z_ascii_117 : forall w,
  ascii_range_list_117 w ->
  word_chars_z_117 w ->
  word_chars (map ascii_of_z_117 w).
Proof.
  intros w Hrange [Hne Hchars].
  split.
  - intro Hnil.
    apply map_eq_nil in Hnil.
    contradiction.
  - clear Hne.
    induction Hchars as [| z zs Hz Hchars IH]; inversion Hrange; subst; simpl.
    + constructor.
    + constructor.
      * intro Hspace.
        apply Hz.
        apply (proj1 (is_space_ascii_z_117 z H1)).
        exact Hspace.
      * apply IH; assumption.
Qed.

Lemma nonempty_spaces_z_ascii_117 : forall xs,
  nonempty_spaces_z_117 xs ->
  nonempty_spaces (map ascii_of_z_117 xs).
Proof.
  intros xs [Hne Hsp].
  split.
  - intro Hnil.
    apply map_eq_nil in Hnil.
    contradiction.
  - apply only_spaces_z_ascii_117; assumption.
Qed.

Lemma separated_words_z_ascii_117 : forall front seps last,
  map ascii_of_z_117 (separated_words_z_117 front seps last) =
  separated_words
    (map (map ascii_of_z_117) front)
    (map (map ascii_of_z_117) seps)
    (map ascii_of_z_117 last).
Proof.
  induction front as [| f front IH]; intros seps last;
    destruct seps as [| sp seps]; simpl; unfold separated_words_z_117; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite map_app.
    simpl.
    rewrite map_app.
    rewrite <- app_assoc.
    rewrite <- map_app.
    change (map ascii_of_z_117
      (List.concat (map (fun ws : list Z * list Z => (fst ws ++ snd ws)%list)
        (combine front seps)) ++ last)%list)
      with (map ascii_of_z_117 (separated_words_z_117 front seps last)).
    rewrite IH.
    unfold separated_words.
    simpl.
    rewrite map_app.
    repeat rewrite app_assoc.
    reflexivity.
Qed.

Lemma split_words_shape_z_ascii_117 : forall s words,
  Forall ascii_range_list_117 words ->
  split_words_shape_z_117 s words ->
  split_words_shape (map ascii_of_z_117 s) (map (map ascii_of_z_117) words).
Proof.
  intros s words Hrange Hshape.
  destruct Hshape as [[Hwords Hspaces] | Hshape].
  - left.
    split.
    + subst words; reflexivity.
    + apply only_spaces_z_ascii_117; assumption.
  - right.
    destruct Hshape as [leading [trailing [front [last [seps Hshape]]]]].
    destruct Hshape as [Hwords [Hwchars [Hlead [Htrail [Hseps [Hlen Heq]]]]]].
    subst words.
    exists (map ascii_of_z_117 leading).
    exists (map ascii_of_z_117 trailing).
    exists (map (map ascii_of_z_117) front).
    exists (map ascii_of_z_117 last).
    exists (map (map ascii_of_z_117) seps).
    repeat split.
    + rewrite map_app.
      reflexivity.
    + change (Forall ascii_range_list_117 (front ++ [last])%list) in Hrange.
      apply Forall_app in Hrange as [Hfront_range Hlast_range].
      change (Forall word_chars_z_117 (front ++ [last])%list) in Hwchars.
      apply Forall_app in Hwchars as [Hfront_words Hlast_words].
      change (Forall word_chars
        (map (map ascii_of_z_117) front ++ [map ascii_of_z_117 last])%list).
      apply Forall_app.
      split.
      * clear -Hfront_words Hfront_range.
        induction Hfront_words; inversion Hfront_range; subst; simpl; constructor; auto.
        apply word_chars_z_ascii_117; assumption.
      * inversion Hlast_range; inversion Hlast_words; subst.
        constructor; [apply word_chars_z_ascii_117; assumption|constructor].
    + apply only_spaces_z_ascii_117; assumption.
    + apply only_spaces_z_ascii_117; assumption.
    + clear -Hseps.
      induction Hseps; simpl; constructor; auto.
      apply nonempty_spaces_z_ascii_117; assumption.
    + rewrite map_length, map_length.
      assumption.
    + subst s.
      repeat rewrite map_app.
      rewrite separated_words_z_ascii_117.
      reflexivity.
Qed.

Lemma count_consonants_ascii_z_117 : forall w,
  ascii_range_list_117 w ->
  Z.of_nat (count_consonants (map ascii_of_z_117 w)) =
  count_consonants_z_117 w.
Proof.
  induction w as [| z zs IH]; intros Hrange; unfold count_consonants in *; simpl; [reflexivity|].
  inversion Hrange; subst.
  rewrite is_consonant_ascii_z_117 by assumption.
  pose proof (IH H2) as Htail.
  destruct (is_consonant_z_117 z); simpl.
  - change (Z.of_nat (S (List.length (filter is_consonant (map ascii_of_z_117 zs)))) =
      1 + count_consonants_z_117 zs).
    rewrite <- Htail; lia.
  - exact Htail.
Qed.

Lemma consonant_filter_ascii_z_117 : forall words need,
  Forall ascii_range_list_117 words ->
  0 <= need ->
  select_words_impl (map (map ascii_of_z_117) words) (Z.to_nat need) =
  map (map ascii_of_z_117)
    (filter (fun w => Z.eqb (count_consonants_z_117 w) need) words).
Proof.
  induction words as [| w ws IH]; intros need Hrange Hneed; simpl; [reflexivity|].
  inversion Hrange; subst.
  pose proof (count_consonants_ascii_z_117 w H1) as Hcount.
  destruct (Nat.eqb_spec (count_consonants (map ascii_of_z_117 w)) (Z.to_nat need)) as [Hnat | Hnat];
    destruct (Z.eqb_spec (count_consonants_z_117 w) need) as [Hz | Hz]; simpl;
    try (rewrite IH by assumption; reflexivity);
    try lia.
Qed.

Lemma problem_117_spec_z_select_output_rows_117 : forall s need,
  all_ascii s ->
  0 <= need ->
  problem_117_spec_z s need (select_output_rows_117 s need).
Proof.
  intros s need Hall Hneed.
  unfold problem_117_spec_z, problem_117_spec.
  rewrite list_ascii_of_string_string_of_list_z_117.
  exists (map (map ascii_of_z_117) (all_payloads_117 s)).
  split.
  - apply split_words_shape_z_ascii_117.
    + apply all_payloads_117_range; assumption.
    + apply all_payloads_117_shape_z.
  - unfold select_output_rows_117.
    rewrite rows_to_strings_c_string_117.
    rewrite select_payloads_117_filter_all.
    rewrite consonant_filter_ascii_z_117 by
      (try apply all_payloads_117_range; assumption).
    rewrite map_map.
    apply map_ext.
    intros payload.
    symmetry.
    apply string_of_list_ascii_map_ascii_of_z_117.
Qed.
