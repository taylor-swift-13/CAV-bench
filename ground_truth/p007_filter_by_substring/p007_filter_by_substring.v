(*  Filter an input list of strings only for ones that contain given substring
>>> filter_by_substring([], 'a')
[]
>>> filter_by_substring(['abc', 'bacd', 'cde', 'array'], 'a')
['abc', 'bacd', 'array']
 *)

(* ∀str, In(str, output) ↔ (In(str, strings) ∧ Contains(str, s))
  ∀i j ∈ [0,length(output)), ∃k l ∈ [0,length(intput)), input[k] = output[i] /\ input[l] = output[j] -> i < j -> k < l
  *)

Require Import List.
Require Import String.
Import ListNotations.

Open Scope string_scope.


(* 判断 s 是否包含子串 sub *)
Fixpoint contains_substring (s sub : string) : bool :=
  match s with
  | EmptyString => if sub =? EmptyString then true else false
  | String _ rest =>
      if String.prefix sub s then true
      else contains_substring rest sub
  end.

Fixpoint filter_by_substring_impl (input : list string) (sub : string) : list string :=
  match input with
  | [] => []
  | h :: t =>
    if contains_substring h sub then
      h :: filter_by_substring_impl t sub
    else
      filter_by_substring_impl t sub
  end.

Definition problem_7_pre : Prop:= True.

Definition problem_7_spec (input output : list string) (sub : string) : Prop :=
  output = filter_by_substring_impl input sub.
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


(* Case-local compatibility with the source proof; DLC intentionally keeps the
   benchmark's pinned string library unchanged. *)
Definition substring_at (str sub : list Z) (i : Z) : Prop :=
  0 <= i <= string_length str /\
  i + string_length sub <= string_length str /\
  forall k, 0 <= k < string_length sub ->
    Znth (i + k) str 0 = Znth k sub 0.

Definition strstr_result (str sub : list Z) (ret s : Z) : Prop :=
  (exists i,
      substring_at str sub i /\
      (forall k, 0 <= k < i -> ~ substring_at str sub k) /\
      ret = s + i /\
      ret <> 0) \/
  ((forall k, 0 <= k <= string_length str -> ~ substring_at str sub k) /\
   ret = 0).
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition ascii_of_z_7 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_7 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_7 c) (string_of_list_z_7 rest)
  end.

Definition row_payload_z_7 (row : list Z) : list Z :=
  firstn (Z.to_nat (Zlength row - 1)) row.

Definition row_string_z_7 (row : list Z) : string :=
  string_of_list_z_7 (row_payload_z_7 row).

Definition rows_to_strings_z_7 (rows : list (list Z)) : list string :=
  map row_string_z_7 rows.

Definition rows_well_formed_7 (rows : list (list Z)) (n : Z) : Prop :=
  Zlength rows = n /\
  forall k,
    0 <= k < n ->
    let row := Znth k rows nil in
    let payload := row_payload_z_7 row in
    row = c_string payload /\
    valid_string payload /\
    string_length payload < INT_MAX.

Definition problem_7_pre_z (rows : list (list Z)) : Prop :=
  problem_7_pre.

Definition problem_7_spec_z
    (rows : list (list Z)) (substring : list Z) (output_rows : list (list Z)) : Prop :=
  problem_7_spec
    (rows_to_strings_z_7 rows)
    (rows_to_strings_z_7 output_rows)
    (string_of_list_z_7 substring).

Definition substring_match_z_7 (row : list Z) (substring : list Z) : Prop :=
  contains_substring (row_string_z_7 row) (string_of_list_z_7 substring) = true.

Fixpoint filter_substring_rows_7
    (rows : list (list Z)) (substring : list Z) : list (list Z) :=
  match rows with
  | [] => []
  | row :: rest =>
      if contains_substring (row_string_z_7 row) (string_of_list_z_7 substring)
      then row :: filter_substring_rows_7 rest substring
      else filter_substring_rows_7 rest substring
  end.

Definition filter_substring_prefix_7
    (rows : list (list Z)) (substring : list Z) (k : Z) : list (list Z) :=
  filter_substring_rows_7 (firstn (Z.to_nat k) rows) substring.

Definition filter_substring_state_7
    (rows : list (list Z)) (substring : list Z) (k : Z)
    (output_rows : list (list Z)) : Prop :=
  0 <= k <= Zlength rows /\
  output_rows = filter_substring_prefix_7 rows substring k.

Lemma rows_well_formed_7_row : forall rows n k,
  rows_well_formed_7 rows n ->
  0 <= k < n ->
  let row := Znth k rows nil in
  let payload := row_payload_z_7 row in
  row = c_string payload /\
  valid_string payload /\
  string_length payload < INT_MAX /\
  Zlength row = string_length payload + 1.
Proof.
  intros rows n k [Hlen Hwf] Hk row payload.
  specialize (Hwf k Hk).
  destruct Hwf as [Hrow [Hvalid Hlt]].
  split; [exact Hrow|].
  split; [exact Hvalid|].
  split; [exact Hlt|].
  subst row payload.
  rewrite Hrow at 1.
  unfold c_string, string_length.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma row_payload_c_string_7 : forall payload,
  row_payload_z_7 (c_string payload) = payload.
Proof.
  intros payload.
  unfold row_payload_z_7, c_string.
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

Lemma c_string_Zlength_7 : forall payload,
  Zlength (c_string payload) = string_length payload + 1.
Proof.
  intros payload.
  unfold c_string, string_length.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma filter_substring_state_7_initial : forall rows substring,
  filter_substring_state_7 rows substring 0 nil.
Proof.
  intros rows substring.
  unfold filter_substring_state_7, filter_substring_prefix_7.
  split; [rewrite Zlength_correct; lia|].
  reflexivity.
Qed.

Lemma firstn_succ_Z_7 : forall (rows : list (list Z)) k,
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

Lemma filter_substring_rows_7_app : forall a b substring,
  filter_substring_rows_7 (a ++ b) substring =
  filter_substring_rows_7 a substring ++ filter_substring_rows_7 b substring.
Proof.
  induction a as [| row rest IH]; simpl; intros b substring.
  - reflexivity.
  - destruct (contains_substring (row_string_z_7 row) (string_of_list_z_7 substring));
      rewrite IH; reflexivity.
Qed.

Lemma filter_substring_prefix_7_step_add : forall rows substring k out,
  filter_substring_state_7 rows substring k out ->
  0 <= k < Zlength rows ->
  substring_match_z_7 (Znth k rows nil) substring ->
  filter_substring_state_7 rows substring (k + 1) (out ++ [Znth k rows nil]).
Proof.
  intros rows substring k out [Hbounds Hout] Hk Hmatch.
  split; [lia|].
  unfold filter_substring_prefix_7 in *.
  rewrite firstn_succ_Z_7 by exact Hk.
  rewrite filter_substring_rows_7_app.
  simpl.
  unfold substring_match_z_7 in Hmatch.
  rewrite Hmatch.
  subst out.
  reflexivity.
Qed.

Lemma filter_substring_prefix_7_step_skip : forall rows substring k out,
  filter_substring_state_7 rows substring k out ->
  0 <= k < Zlength rows ->
  ~ substring_match_z_7 (Znth k rows nil) substring ->
  filter_substring_state_7 rows substring (k + 1) out.
Proof.
  intros rows substring k out [Hbounds Hout] Hk Hnomatch.
  split; [lia|].
  unfold filter_substring_prefix_7 in *.
  rewrite firstn_succ_Z_7 by exact Hk.
  rewrite filter_substring_rows_7_app.
  simpl.
  destruct (contains_substring (row_string_z_7 (Znth k rows nil))
              (string_of_list_z_7 substring)) eqn:Hcontains.
  - exfalso; apply Hnomatch; exact Hcontains.
  - rewrite app_nil_r.
    exact Hout.
Qed.

Lemma filter_substring_rows_7_map : forall rows substring,
  rows_to_strings_z_7 (filter_substring_rows_7 rows substring) =
  filter_by_substring_impl (rows_to_strings_z_7 rows) (string_of_list_z_7 substring).
Proof.
  induction rows as [| row rest IH]; intros substring; simpl.
  - reflexivity.
  - unfold rows_to_strings_z_7 in *; simpl in *.
    destruct (contains_substring (row_string_z_7 row) (string_of_list_z_7 substring));
      simpl; rewrite IH; reflexivity.
Qed.

Lemma problem_7_spec_z_of_filter_state : forall rows substring output_rows,
  filter_substring_state_7 rows substring (Zlength rows) output_rows ->
  problem_7_spec_z rows substring output_rows.
Proof.
  intros rows substring output_rows [_ Hout].
  unfold problem_7_spec_z, problem_7_spec.
  unfold filter_substring_prefix_7 in Hout.
  rewrite firstn_all2 in Hout by (rewrite Zlength_correct; lia).
  subst output_rows.
  rewrite filter_substring_rows_7_map.
  reflexivity.
Qed.

Lemma String_length_string_of_list_z_7 : forall l,
  String.length (string_of_list_z_7 l) = List.length l.
Proof.
  induction l as [| x xs IH]; simpl; congruence.
Qed.

Lemma ascii_of_z_7_inj_ascii : forall a b,
  0 <= a <= 127 ->
  0 <= b <= 127 ->
  ascii_of_z_7 a = ascii_of_z_7 b ->
  a = b.
Proof.
  intros a b Ha Hb Heq.
  unfold ascii_of_z_7 in Heq.
  apply f_equal with (f := nat_of_ascii) in Heq.
  repeat rewrite nat_ascii_embedding in Heq by lia.
  lia.
Qed.

Lemma string_prefix_true_of_z_eq_7 : forall prefix row,
  Zlength prefix <= Zlength row ->
  (forall k, 0 <= k < Zlength prefix -> Znth k row 0 = Znth k prefix 0) ->
  String.prefix (string_of_list_z_7 prefix) (string_of_list_z_7 row) = true.
Proof.
  induction prefix as [| pc ps IH]; intros row Hlen Heq; simpl.
  - destruct row; reflexivity.
  - destruct row as [| rc rs]; simpl in *.
    + rewrite Zlength_cons, Zlength_nil in Hlen.
      pose proof (Zlength_nonneg ps).
      lia.
    + rewrite !Zlength_cons in Hlen.
      assert (Hhead : rc = pc).
      {
        assert (H0 : 0 <= 0 < Zlength (pc :: ps)).
        { rewrite Zlength_cons. pose proof (Zlength_nonneg ps). lia. }
        specialize (Heq 0 H0).
        simpl in Heq.
        exact Heq.
      }
      subst rc.
      destruct (ascii_dec (ascii_of_z_7 pc) (ascii_of_z_7 pc)) as [_ | Hneq].
      * apply IH.
        -- lia.
        -- intros k Hk.
           specialize (Heq (k + 1)).
           rewrite !Znth_cons in Heq by lia.
           replace (k + 1 - 1) with k in Heq by lia.
           apply Heq.
           rewrite Zlength_cons.
           pose proof (Zlength_nonneg ps).
           lia.
      * contradiction.
Qed.

Lemma string_prefix_true_ascii_eq_7 : forall prefix row k,
  String.prefix (string_of_list_z_7 prefix) (string_of_list_z_7 row) = true ->
  0 <= k < Zlength prefix ->
  ascii_of_z_7 (Znth k prefix 0) = ascii_of_z_7 (Znth k row 0).
Proof.
  induction prefix as [| pc ps IH]; intros row k Hpref Hk; simpl in Hpref.
  - rewrite Zlength_nil in Hk; lia.
  - destruct row as [| rc rs]; simpl in Hpref.
    + discriminate.
    + rewrite Zlength_cons in Hk.
      destruct (ascii_dec (ascii_of_z_7 pc) (ascii_of_z_7 rc)) as [Heq | Hneq].
      * destruct (Z.eq_dec k 0) as [-> | Hnz].
        -- simpl. exact Heq.
        -- rewrite !Znth_cons by lia.
           apply IH; [exact Hpref | lia].
      * discriminate.
Qed.

Lemma string_prefix_true_length_7 : forall prefix row,
  String.prefix (string_of_list_z_7 prefix) (string_of_list_z_7 row) = true ->
  Zlength prefix <= Zlength row.
Proof.
  induction prefix as [| pc ps IH]; intros row Hpref.
  - rewrite Zlength_nil.
    apply Zlength_nonneg.
  - destruct row as [| rc rs]; simpl in Hpref.
    + discriminate.
    + destruct (ascii_dec (ascii_of_z_7 pc) (ascii_of_z_7 rc)) as [_ | Hneq];
        [| discriminate].
      rewrite !Zlength_cons.
      specialize (IH rs Hpref).
      lia.
Qed.

Lemma valid_string_tail_7 : forall x xs,
  valid_string (x :: xs) -> valid_string xs.
Proof.
  intros x xs [Hascii Hno].
  split.
  - intros i Hi.
    specialize (Hascii (i + 1)).
    rewrite Znth_cons in Hascii by lia.
    replace (i + 1 - 1) with i in Hascii by lia.
    apply Hascii.
    rewrite Zlength_cons.
    pose proof (Zlength_nonneg xs).
    lia.
  - intros i Hi.
    specialize (Hno (i + 1)).
    rewrite Znth_cons in Hno by lia.
    replace (i + 1 - 1) with i in Hno by lia.
    apply Hno.
    rewrite Zlength_cons.
    pose proof (Zlength_nonneg xs).
    lia.
Qed.

Lemma string_prefix_true_to_substring_at_7 : forall payload sub,
  valid_string payload ->
  valid_string sub ->
  String.prefix (string_of_list_z_7 sub) (string_of_list_z_7 payload) = true ->
  substring_at payload sub 0.
Proof.
  intros payload sub Hpayload Hsub Hpref.
  unfold substring_at, string_length.
  split.
  - pose proof (Zlength_nonneg payload); lia.
  - split.
    + apply string_prefix_true_length_7 in Hpref.
      lia.
    + intros k Hk.
      pose proof (string_prefix_true_length_7 sub payload Hpref) as Hpref_len.
      assert (Hascii := string_prefix_true_ascii_eq_7 sub payload k Hpref Hk).
      destruct Hpayload as [Hpayload_ascii _].
      destruct Hsub as [Hsub_ascii _].
      rewrite Z.add_0_l.
      apply ascii_of_z_7_inj_ascii.
      * apply Hpayload_ascii. unfold string_length in Hk. lia.
      * apply Hsub_ascii. unfold string_length in Hk. lia.
      * symmetry; exact Hascii.
Qed.

Lemma substring_at_zero_to_prefix_true_7 : forall payload sub,
  substring_at payload sub 0 ->
  String.prefix (string_of_list_z_7 sub) (string_of_list_z_7 payload) = true.
Proof.
  intros payload sub [Hbounds [Hlen Hchars]].
  apply string_prefix_true_of_z_eq_7.
  - unfold string_length in Hlen; lia.
  - intros k Hk.
    specialize (Hchars k).
    rewrite Z.add_0_l in Hchars.
    apply Hchars.
    unfold string_length in *; lia.
Qed.

Lemma contains_substring_tail_true_7 : forall c s sub,
  contains_substring s sub = true ->
  contains_substring (String c s) sub = true.
Proof.
  intros c s sub H.
  destruct sub as [| a sub']; simpl.
  - reflexivity.
  - destruct (ascii_dec a c).
    + destruct (String.prefix sub' s); [reflexivity | exact H].
    + exact H.
Qed.

Lemma contains_substring_prefix_true_7 : forall s sub,
  String.prefix sub s = true ->
  contains_substring s sub = true.
Proof.
  intros s sub Hpref.
  destruct s as [| c rest].
  - destruct sub as [| a sub']; simpl in *; [reflexivity | discriminate].
  - destruct sub as [| a sub']; simpl in *.
    + reflexivity.
    + destruct (ascii_dec a c) as [_ | Hneq].
      * rewrite Hpref. reflexivity.
      * discriminate.
Qed.

Lemma substring_at_tail_7 : forall x xs sub i,
  substring_at (x :: xs) sub i ->
  0 < i ->
  substring_at xs sub (i - 1).
Proof.
  intros x xs sub i [Hbounds [Hlen Hchars]] Hi.
  unfold substring_at, string_length in *.
  rewrite Zlength_cons in *.
  split; [lia|].
  split; [lia|].
  intros k Hk.
  specialize (Hchars k Hk).
  rewrite Znth_cons in Hchars by lia.
  replace (i + k - 1) with (i - 1 + k) in Hchars by lia.
  exact Hchars.
Qed.

Lemma substring_at_lift_tail_7 : forall x xs sub i,
  substring_at xs sub i ->
  substring_at (x :: xs) sub (i + 1).
Proof.
  intros x xs sub i [Hbounds [Hlen Hchars]].
  unfold substring_at, string_length in *.
  rewrite Zlength_cons.
  split; [lia|].
  split; [lia|].
  intros k Hk.
  rewrite Znth_cons by lia.
  replace (i + 1 + k - 1) with (i + k) by lia.
  apply Hchars.
  exact Hk.
Qed.

Lemma contains_substring_of_substring_at_7 : forall payload sub i,
  substring_at payload sub i ->
  contains_substring (string_of_list_z_7 payload) (string_of_list_z_7 sub) = true.
Proof.
  induction payload as [| x xs IH]; intros sub i Hsubat.
  - unfold substring_at, string_length in Hsubat.
    rewrite Zlength_nil in Hsubat.
    destruct Hsubat as [Hi [Hlen _]].
    destruct sub as [| y ys].
    + reflexivity.
    + rewrite Zlength_cons in Hlen.
      change (Z.succ (Zlength ys)) with (Zlength ys + 1) in Hlen.
      pose proof (Zlength_nonneg ys).
      lia.
  - destruct (Z.eq_dec i 0) as [Hi0 | Hnz].
    + subst i.
      apply contains_substring_prefix_true_7.
      apply substring_at_zero_to_prefix_true_7.
      exact Hsubat.
    + apply contains_substring_tail_true_7.
      apply IH with (i := i - 1).
      apply substring_at_tail_7 with (x := x).
      * exact Hsubat.
      * destruct Hsubat as [Hbounds _]; lia.
Qed.

Lemma contains_substring_to_substring_at_7 : forall payload sub,
  valid_string payload ->
  valid_string sub ->
  contains_substring (string_of_list_z_7 payload) (string_of_list_z_7 sub) = true ->
  exists i, substring_at payload sub i.
Proof.
  induction payload as [| x xs IH]; intros sub Hpayload Hsub Hcontains.
  - simpl in Hcontains.
    destruct (string_of_list_z_7 sub =? EmptyString)%string eqn:Heq; [| discriminate].
    destruct sub as [| y ys].
    + exists 0.
      unfold substring_at, string_length.
      repeat rewrite Zlength_nil.
      split; [lia| split; [lia| intros k Hk; lia]].
    + simpl in Heq.
      discriminate.
  - simpl in Hcontains.
    destruct (String.prefix (string_of_list_z_7 sub)
               (String (ascii_of_z_7 x) (string_of_list_z_7 xs))) eqn:Hpref.
    + exists 0.
      apply string_prefix_true_to_substring_at_7; auto.
    + pose proof (valid_string_tail_7 x xs Hpayload) as Hxs.
      simpl in Hpref.
      rewrite Hpref in Hcontains.
      specialize (IH sub Hxs Hsub Hcontains).
      destruct IH as [i Hi].
      exists (i + 1).
      apply substring_at_lift_tail_7.
      exact Hi.
Qed.

Lemma strstr_result_contains_match_7 : forall row sub ret base,
  strstr_result (row_payload_z_7 row) sub ret base ->
  ret <> 0 ->
  substring_match_z_7 row sub.
Proof.
  intros row sub ret base Hresult Hret.
  unfold strstr_result in Hresult.
  destruct Hresult as [[i [Hsubat [_ [Hret_eq Hret_nonzero]]]] | [_ Hzero]].
  - unfold substring_match_z_7, row_string_z_7.
    apply contains_substring_of_substring_at_7 with (i := i).
    exact Hsubat.
  - subst ret. contradiction.
Qed.

Lemma strstr_result_no_match_7 : forall row sub ret base,
  valid_string (row_payload_z_7 row) ->
  valid_string sub ->
  strstr_result (row_payload_z_7 row) sub ret base ->
  ret = 0 ->
  ~ substring_match_z_7 row sub.
Proof.
  intros row sub ret base Hrow Hsub Hresult Hret Hmatch.
  unfold substring_match_z_7, row_string_z_7 in Hmatch.
  pose proof (contains_substring_to_substring_at_7
    (row_payload_z_7 row) sub Hrow Hsub Hmatch) as [i Hsubat].
  unfold strstr_result in Hresult.
  destruct Hresult as [[j [_ [_ [_ Hret_nonzero]]]] | [Hnone Hzero]].
  - subst ret. contradiction.
  - apply (Hnone i).
    + destruct Hsubat as [Hi _].
      exact Hi.
    + exact Hsubat.
Qed.
