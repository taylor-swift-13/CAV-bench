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

Lemma Zlength_rev_112 : forall {A : Type} (l : list A),
  Zlength (rev l) = Zlength l.
Proof.
  intros A l.
  repeat rewrite Zlength_correct.
  rewrite rev_length.
  reflexivity.
Qed.

Lemma Znth_rev_112 : forall {A : Type} (l : list A) (d : A) i,
  0 <= i < Zlength l ->
  Znth i (rev l) d = Znth (Zlength l - 1 - i) l d.
Proof.
  intros A l d i Hi.
  unfold Znth.
  rewrite rev_nth.
  - assert (Hnat :
      Z.to_nat (Zlength l - 1 - i) =
      (List.length l - S (Z.to_nat i))%nat).
    { apply Nat2Z.inj.
      rewrite Z2Nat.id by lia.
      rewrite Nat2Z.inj_sub by (rewrite Zlength_correct in Hi; lia).
      rewrite Nat2Z.inj_succ.
      rewrite Z2Nat.id by lia.
      rewrite Zlength_correct.
      lia. }
    rewrite Hnat.
    reflexivity.
  - rewrite Zlength_correct in Hi.
    lia.
Qed.

Lemma String_length_string_of_list_z_112 : forall l,
  String.length (string_of_list_z_112 l) = List.length l.
Proof.
  induction l as [| x xs IH]; simpl; congruence.
Qed.

Lemma string_of_list_ascii_map_ascii_of_z_112 : forall s,
  string_of_list_ascii (map ascii_of_z_112 s) = string_of_list_z_112 s.
Proof.
  induction s as [| x xs IH]; simpl; congruence.
Qed.

Lemma list_ascii_of_string_string_of_list_z_112 : forall s,
  list_ascii_of_string (string_of_list_z_112 s) =
  map ascii_of_z_112 s.
Proof.
  induction s as [| x xs IH]; simpl; congruence.
Qed.

Lemma ascii_of_z_112_nat_of_ascii : forall z,
  0 <= z < 256 ->
  nat_of_ascii (ascii_of_z_112 z) = Z.to_nat z.
Proof.
  intros z Hz.
  unfold ascii_of_z_112.
  rewrite nat_ascii_embedding by lia.
  reflexivity.
Qed.

Lemma ascii_of_z_112_inj_range : forall a b,
  0 <= a < 256 ->
  0 <= b < 256 ->
  ascii_of_z_112 a = ascii_of_z_112 b ->
  a = b.
Proof.
  intros a b Ha Hb Heq.
  apply (f_equal nat_of_ascii) in Heq.
  rewrite !ascii_of_z_112_nat_of_ascii in Heq by lia.
  lia.
Qed.

Lemma ascii_of_z_112_eqb : forall a b,
  0 <= a < 256 ->
  0 <= b < 256 ->
  Ascii.eqb (ascii_of_z_112 a) (ascii_of_z_112 b) = Z.eqb a b.
Proof.
  intros a b Ha Hb.
  destruct (Ascii.eqb_spec (ascii_of_z_112 a) (ascii_of_z_112 b)) as [Heq | Hneq];
    destruct (Z.eqb_spec a b) as [Hz | Hz]; subst; try reflexivity.
  - exfalso. apply Hz. eapply ascii_of_z_112_inj_range; eauto.
  - exfalso. apply Hneq. reflexivity.
Qed.

Lemma valid_lower_payload_112_tail : forall x xs,
  valid_lower_payload_112 (x :: xs) ->
  valid_lower_payload_112 xs.
Proof.
  intros x xs H i Hi.
  specialize (H (i + 1)).
  rewrite Znth_cons in H by lia.
  replace (i + 1 - 1) with i in H by lia.
  apply H.
  rewrite Zlength_cons.
  lia.
Qed.

Lemma valid_lower_payload_112_head : forall x xs,
  valid_lower_payload_112 (x :: xs) ->
  97 <= x <= 122.
Proof.
  intros x xs H.
  specialize (H 0).
  rewrite Znth0_cons in H.
  apply H.
  rewrite Zlength_cons.
  pose proof (Zlength_nonneg xs).
  lia.
Qed.

Lemma valid_lower_payload_112_range : forall s i,
  valid_lower_payload_112 s ->
  0 <= i < Zlength s ->
  0 <= Znth i s 0 < 256.
Proof.
  intros s i H Hi.
  specialize (H i Hi).
  lia.
Qed.

Lemma valid_lower_payload_112_In_range : forall s x,
  valid_lower_payload_112 s ->
  In x s ->
  0 <= x < 256.
Proof.
  intros s x Hvalid Hin.
  destruct (In_nth s x 0 Hin) as [n [Hn Hnth]].
  specialize (Hvalid (Z.of_nat n)).
  unfold Znth in Hvalid.
  rewrite Nat2Z.id in Hvalid.
  rewrite Hnth in Hvalid.
  assert (Hb : 0 <= Z.of_nat n < Zlength s).
  { apply Nat2Z.inj_lt in Hn.
    rewrite Zlength_correct.
    lia. }
  specialize (Hvalid Hb).
  lia.
Qed.

Lemma existsb_ascii_char_in_zb_112 : forall x c,
  0 <= x < 256 ->
  valid_lower_payload_112 c ->
  spec_existsb_112 (fun a : ascii => Ascii.eqb a (ascii_of_z_112 x))
    (map ascii_of_z_112 c) =
  char_in_zb_112 x c.
Proof.
  intros x c Hx Hc.
  induction c as [| y ys IH]; simpl; [reflexivity|].
  assert (Hy : 0 <= y < 256).
  { pose proof (valid_lower_payload_112_head y ys Hc). lia. }
  rewrite ascii_of_z_112_eqb by (try exact Hx; exact Hy).
  rewrite Z.eqb_sym.
  destruct (Z.eqb x y); simpl.
  - reflexivity.
  - apply IH. apply valid_lower_payload_112_tail in Hc. exact Hc.
Qed.

Lemma delete_chars_impl_map_ascii_of_z_112 : forall s c,
  valid_lower_payload_112 s ->
  valid_lower_payload_112 c ->
  delete_chars_impl (map ascii_of_z_112 s) (map ascii_of_z_112 c) =
  map ascii_of_z_112 (filter_not_in_z_112 s c).
Proof.
  intros s c Hs Hc.
  induction s as [| x xs IH]; simpl; [reflexivity|].
  assert (Hx : 0 <= x < 256).
  { pose proof (valid_lower_payload_112_head x xs Hs). lia. }
  rewrite existsb_ascii_char_in_zb_112 by (exact Hx || exact Hc).
  destruct (char_in_zb_112 x c); simpl;
    rewrite IH by (apply valid_lower_payload_112_tail in Hs; exact Hs);
    reflexivity.
Qed.

Lemma filter_not_in_z_112_valid_lower : forall s c,
  valid_lower_payload_112 s ->
  valid_lower_payload_112 (filter_not_in_z_112 s c).
Proof.
  intros s c Hs.
  induction s as [| x xs IH]; simpl.
  - intros i Hi. rewrite Zlength_nil in Hi. lia.
  - destruct (char_in_zb_112 x c).
    + apply IH. apply valid_lower_payload_112_tail in Hs. exact Hs.
    + intros i Hi.
      destruct (Z.eq_dec i 0) as [-> | Hne].
      * rewrite Znth0_cons.
        apply valid_lower_payload_112_head in Hs. exact Hs.
      * rewrite Znth_cons by lia.
        apply IH.
        -- apply valid_lower_payload_112_tail in Hs. exact Hs.
        -- rewrite Zlength_cons in Hi. lia.
Qed.

Lemma spec_list_eqb_Z_true_eq_112 : forall a b,
  spec_list_eqb_112 Z.eqb a b = true ->
  a = b.
Proof.
  induction a as [| x xs IH]; intros [| y ys] H; simpl in H; try discriminate; auto.
  apply andb_true_iff in H as [Hxy Htail].
  apply Z.eqb_eq in Hxy.
  subst y.
  f_equal.
  apply IH. exact Htail.
Qed.

Lemma spec_list_eqb_Z_true_by_pointwise_112 : forall a b,
  Zlength a = Zlength b ->
  (forall i, 0 <= i < Zlength a -> Znth i a 0 = Znth i b 0) ->
  spec_list_eqb_112 Z.eqb a b = true.
Proof.
  induction a as [| x xs IH]; intros [| y ys] Hlen Hnth; simpl in *; try reflexivity.
  - rewrite Zlength_nil in Hlen. rewrite Zlength_cons in Hlen.
    pose proof (Zlength_nonneg ys). lia.
  - rewrite Zlength_cons in Hlen. rewrite Zlength_nil in Hlen.
    pose proof (Zlength_nonneg xs). lia.
  - apply andb_true_iff.
    split.
    + apply Z.eqb_eq.
      specialize (Hnth 0).
      rewrite !Znth0_cons in Hnth.
      apply Hnth.
      rewrite Zlength_cons.
      pose proof (Zlength_nonneg xs). lia.
    + apply IH.
      * rewrite !Zlength_cons in Hlen. lia.
      * intros i Hi.
        specialize (Hnth (i + 1)).
        rewrite !Znth_cons in Hnth by lia.
        replace (i + 1 - 1) with i in Hnth by lia.
        apply Hnth.
        rewrite Zlength_cons.
        lia.
Qed.

Lemma spec_list_eqb_Z_false_by_Znth_112 : forall a b i,
  Zlength a = Zlength b ->
  0 <= i < Zlength a ->
  Znth i a 0 <> Znth i b 0 ->
  spec_list_eqb_112 Z.eqb a b = false.
Proof.
  intros a b i Hlen Hi Hneq.
  destruct (spec_list_eqb_112 Z.eqb a b) eqn:Heq; [| reflexivity].
  apply spec_list_eqb_Z_true_eq_112 in Heq.
  subst b.
  contradiction.
Qed.

Lemma pal_bool_112_true_of_mirror : forall s,
  mirror_prefix_112 s (Zlength s ÷ 2) ->
  pal_bool_112 s = true.
Proof.
  intros s Hmirror.
  unfold mirror_prefix_112 in Hmirror.
  unfold pal_bool_112.
  apply spec_list_eqb_Z_true_by_pointwise_112.
  - rewrite Zlength_rev_112. reflexivity.
  - intros i Hi.
    rewrite Znth_rev_112 by lia.
    destruct (Z_lt_ge_dec i (Zlength s - 1 - i)) as [Hlt | Hge].
    + apply Hmirror. split; [lia|].
      assert (i + 1 <= Zlength s ÷ 2).
      { apply (Z.quot_le_lower_bound (Zlength s) 2 (i + 1)); lia. }
      lia.
    + destruct (Z.eq_dec i (Zlength s - 1 - i)) as [Heq | Hneq].
      * replace (Zlength s - 1 - i) with i by lia. reflexivity.
      * symmetry.
        replace i with (Zlength s - 1 - (Zlength s - 1 - i)) at 2 by lia.
        apply Hmirror. split; [lia|].
        assert (Zlength s - 1 - i + 1 <= Zlength s ÷ 2).
        { apply (Z.quot_le_lower_bound (Zlength s) 2 (Zlength s - 1 - i + 1)); lia. }
        lia.
Qed.

Lemma pal_bool_112_false_of_mismatch : forall s,
  mirror_mismatch_prefix_112 s (Zlength s ÷ 2) ->
  pal_bool_112 s = false.
Proof.
  intros s [i [Hi Hneq]].
  unfold pal_bool_112.
  apply (spec_list_eqb_Z_false_by_Znth_112 s (rev s) i).
  - rewrite Zlength_rev_112. reflexivity.
  - pose proof (Zlength_nonneg s).
    assert (Zlength s ÷ 2 <= Zlength s).
    { apply (Z.quot_le_upper_bound (Zlength s) 2 (Zlength s)); lia. }
    lia.
  - rewrite Znth_rev_112.
    + exact Hneq.
    + pose proof (Zlength_nonneg s).
      assert (Zlength s ÷ 2 <= Zlength s).
      { apply (Z.quot_le_upper_bound (Zlength s) 2 (Zlength s)); lia. }
      lia.
Qed.

Lemma palindrome_scan_state_112_true_full : forall s,
  palindrome_scan_state_112 s (Zlength s ÷ 2) 1 ->
  pal_bool_112 s = true.
Proof.
  intros s [_ [Htrue _]].
  apply pal_bool_112_true_of_mirror.
  apply Htrue. reflexivity.
Qed.

Lemma palindrome_scan_state_112_false_full : forall s,
  palindrome_scan_state_112 s (Zlength s ÷ 2) 0 ->
  pal_bool_112 s = false.
Proof.
  intros s [_ [_ [Hfalse _]]].
  apply pal_bool_112_false_of_mismatch.
  apply Hfalse. reflexivity.
Qed.

Lemma spec_list_eqb_ascii_map_z_112 : forall a b,
  (forall x, In x a -> 0 <= x < 256) ->
  (forall x, In x b -> 0 <= x < 256) ->
  spec_list_eqb_112 Ascii.eqb (map ascii_of_z_112 a) (map ascii_of_z_112 b) =
  spec_list_eqb_112 Z.eqb a b.
Proof.
  induction a as [| x xs IH]; intros [| y ys] Ha Hb; simpl; try reflexivity.
  rewrite ascii_of_z_112_eqb by (apply Ha + apply Hb; simpl; auto).
  assert (Hxs : forall z : Z, In z xs -> 0 <= z < 256).
  { intros z Hz. apply Ha. simpl. auto. }
  assert (Hys : forall z : Z, In z ys -> 0 <= z < 256).
  { intros z Hz. apply Hb. simpl. auto. }
  rewrite IH by (exact Hxs || exact Hys).
  reflexivity.
Qed.

Lemma is_pal_impl_map_ascii_of_z_112 : forall s,
  (forall x, In x s -> 0 <= x < 256) ->
  is_pal_impl (map ascii_of_z_112 s) = pal_bool_112 s.
Proof.
  intros s Hrange.
  unfold is_pal_impl, pal_bool_112.
  rewrite <- map_rev.
  apply spec_list_eqb_ascii_map_z_112.
  - exact Hrange.
  - intros x Hx. apply Hrange. apply in_rev. exact Hx.
Qed.

Lemma char_in_zb_112_true_iff : forall c s,
  char_in_zb_112 c s = true <-> char_in_z_112 c s.
Proof.
  intros c s.
  induction s as [| x xs IH]; simpl.
  - split; intros H; [discriminate|contradiction].
  - destruct (Z.eqb_spec c x) as [Heq | Hneq].
    + subst. split; intros _; [left; reflexivity|reflexivity].
    + rewrite IH.
      split.
      * intros H. right; exact H.
      * intros [H | H]; [congruence|exact H].
Qed.

Lemma char_in_zb_112_false_iff : forall c s,
  char_in_zb_112 c s = false <-> ~ char_in_z_112 c s.
Proof.
  intros c s.
  rewrite <- char_in_zb_112_true_iff.
  destruct (char_in_zb_112 c s) eqn:H; split; simpl; intros Hx; try discriminate; try congruence.
Qed.

Lemma filter_prefix_state_112_initial : forall s c,
  filter_prefix_state_112 s c 0 [].
Proof.
  intros s c.
  unfold filter_prefix_state_112.
  split; [rewrite Zlength_correct; lia|].
  reflexivity.
Qed.

Lemma sublist_0_succ_Z_112 : forall (s : list Z) i,
  0 <= i < Zlength s ->
  sublist 0 (i + 1) s = sublist 0 i s ++ [Znth i s 0].
Proof.
  intros s i Hi.
  rewrite (sublist_split 0 (i + 1) i s) by lia.
  replace (sublist i (i + 1) s) with [Znth i s 0].
  - reflexivity.
  - symmetry. apply sublist_single. lia.
Qed.

Lemma filter_not_in_z_112_app_single_add : forall p c x,
  char_in_zb_112 x c = false ->
  filter_not_in_z_112 (p ++ [x]) c =
  filter_not_in_z_112 p c ++ [x].
Proof.
  induction p as [| y ys IH]; intros c x Hx; simpl.
  - rewrite Hx. reflexivity.
  - destruct (char_in_zb_112 y c); rewrite IH by exact Hx; reflexivity.
Qed.

Lemma filter_not_in_z_112_app_single_skip : forall p c x,
  char_in_zb_112 x c = true ->
  filter_not_in_z_112 (p ++ [x]) c =
  filter_not_in_z_112 p c.
Proof.
  induction p as [| y ys IH]; intros c x Hx; simpl.
  - rewrite Hx. reflexivity.
  - destruct (char_in_zb_112 y c); rewrite IH by exact Hx; reflexivity.
Qed.

Lemma filter_prefix_state_112_step_add : forall s c i out,
  filter_prefix_state_112 s c i out ->
  0 <= i < Zlength s ->
  ~ char_in_z_112 (Znth i s 0) c ->
  filter_prefix_state_112 s c (i + 1) (out ++ [Znth i s 0]).
Proof.
  intros s c i out [Hb Hout] Hi Hnot.
  split; [lia|].
  rewrite sublist_0_succ_Z_112 by lia.
  rewrite filter_not_in_z_112_app_single_add.
  - subst out. reflexivity.
  - apply char_in_zb_112_false_iff. exact Hnot.
Qed.

Lemma filter_prefix_state_112_step_skip : forall s c i out,
  filter_prefix_state_112 s c i out ->
  0 <= i < Zlength s ->
  char_in_z_112 (Znth i s 0) c ->
  filter_prefix_state_112 s c (i + 1) out.
Proof.
  intros s c i out [Hb Hout] Hi Hin.
  split; [lia|].
  rewrite sublist_0_succ_Z_112 by lia.
  rewrite filter_not_in_z_112_app_single_skip.
  - exact Hout.
  - apply char_in_zb_112_true_iff. exact Hin.
Qed.

Lemma c_string_Znth_inside_112 : forall s i,
  0 <= i < string_length s ->
  Znth i (c_string s) 0 = Znth i s 0.
Proof.
  intros s i Hi.
  apply c_string_Znth_inside.
  exact Hi.
Qed.

Lemma valid_reverse_delete_input_112_s_char_range : forall s c i,
  valid_reverse_delete_input_112 s c ->
  0 <= i < string_length s ->
  0 <= Znth i (c_string s) 0 <= 127 /\
  Znth i (c_string s) 0 <> 0.
Proof.
  intros s c i [Hs _] Hi.
  rewrite c_string_Znth_inside_112 by exact Hi.
  specialize (Hs i Hi).
  split; lia.
Qed.

Lemma Znth_In_range_112 : forall (l : list Z) k d,
  0 <= k < Zlength l ->
  In (Znth k l d) l.
Proof.
  intros l k d Hk.
  unfold Znth.
  apply nth_In.
  apply Nat2Z.inj_lt.
  rewrite Z2Nat.id by lia.
  rewrite <- Zlength_correct.
  lia.
Qed.

Lemma strchr_result_zero_not_in_112 : forall c_l ch base,
  strchr_result c_l ch 0 base ->
  ch <> 0 ->
  ~ char_in_z_112 ch c_l.
Proof.
  intros c_l ch base Hres Hnz Hin.
  unfold strchr_result in Hres.
  destruct Hres as [[j [Hj [Hval [_ [_ Hret_nonzero]]]]] |
                    [Hnone [[Hch0 _] | [_ Hret]]]].
  - contradiction.
  - contradiction.
  - unfold char_in_z_112 in Hin.
    destruct (In_nth c_l ch 0 Hin) as [n [Hn Hnth]].
    specialize (Hnone (Z.of_nat n)).
    unfold Znth in Hnone.
    rewrite Nat2Z.id in Hnone.
    apply Hnone.
    + unfold string_length.
      split; [apply Nat2Z.is_nonneg|].
      change (Z.of_nat n < Zlength c_l).
      rewrite Zlength_correct.
      apply (proj1 (Nat2Z.inj_lt n (Datatypes.length c_l))).
      exact Hn.
    + exact Hnth.
Qed.

Lemma strchr_result_nonzero_in_112 : forall c_l ch ret base,
  strchr_result c_l ch ret base ->
  ret <> 0 ->
  ch <> 0 ->
  char_in_z_112 ch c_l.
Proof.
  intros c_l ch ret base Hres Hret_ne Hch_ne.
  unfold strchr_result in Hres.
  destruct Hres as [[j [Hj [Hval [_ [_ _]]]]] |
                    [Hnone [[Hch0 Hret] | [Hch Hret]]]].
  - unfold char_in_z_112.
    rewrite <- Hval.
    apply Znth_In_range_112.
    exact Hj.
  - contradiction.
  - contradiction.
Qed.

Lemma filter_prefix_state_112_full : forall s c out,
  filter_prefix_state_112 s c (Zlength s) out ->
  out = filter_not_in_z_112 s c.
Proof.
  intros s c out [_ Hout].
  unfold string_length in *.
  rewrite sublist_self in Hout by lia.
  exact Hout.
Qed.

Lemma Zlength_filter_not_in_z_112_le : forall s c,
  Zlength (filter_not_in_z_112 s c) <= Zlength s.
Proof.
  induction s as [| x xs IH]; intros c; simpl.
  - lia.
  - rewrite Zlength_cons.
    destruct (char_in_zb_112 x c).
    + specialize (IH c). lia.
    + rewrite Zlength_cons.
      specialize (IH c). lia.
Qed.

Lemma filter_prefix_state_112_length_le : forall s c i out,
  filter_prefix_state_112 s c i out ->
  Zlength out <= i.
Proof.
  intros s c i out [Hi Hout].
  subst out.
  pose proof (Zlength_filter_not_in_z_112_le (sublist 0 i s) c).
  rewrite Zlength_sublist in H by lia.
  lia.
Qed.

Lemma palindrome_scan_state_112_initial : forall s,
  palindrome_scan_state_112 s 0 1.
Proof.
  intros s.
  unfold palindrome_scan_state_112.
  split; [pose proof (Zlength_nonneg s); lia|].
  split.
  - intros _. unfold mirror_prefix_112. intros k Hk. lia.
  - split.
    + intros H; discriminate.
    + right; reflexivity.
Qed.

Lemma palindrome_scan_state_112_step_match : forall s i,
  palindrome_scan_state_112 s i 1 ->
  0 <= i /\ i + 1 <= Zlength s ->
  Znth i s 0 = Znth (Zlength s - 1 - i) s 0 ->
  palindrome_scan_state_112 s (i + 1) 1.
Proof.
  intros s i [Hb [Hpal [_ Hcase]]] Hi Heq.
  split; [lia|].
  split.
  - intros _ k Hk.
    destruct (Z.eq_dec k i) as [-> | Hne].
    + exact Heq.
    + apply Hpal; [reflexivity|lia].
  - split; [intros H; discriminate|right; reflexivity].
Qed.

Lemma palindrome_scan_state_112_step_mismatch : forall s i,
  palindrome_scan_state_112 s i 1 ->
  0 <= i /\ i + 1 <= Zlength s ->
  Znth i s 0 <> Znth (Zlength s - 1 - i) s 0 ->
  palindrome_scan_state_112 s (i + 1) 0.
Proof.
  intros s i [Hb _] Hi Hneq.
  split; [lia|].
  split; [intros H; discriminate|].
  split.
  - intros _. exists i. split; [lia|exact Hneq].
  - left; reflexivity.
Qed.

Lemma palindrome_scan_state_112_step_false : forall s i,
  palindrome_scan_state_112 s i 0 ->
  0 <= i /\ i + 1 <= Zlength s ->
  palindrome_scan_state_112 s (i + 1) 0.
Proof.
  intros s i [Hb [_ [Hmis _]]] Hi.
  split; [lia|].
  split; [intros H; discriminate|].
  split.
  - intros _.
    destruct (Hmis eq_refl) as [k [Hk Hneq]].
    exists k. split; [lia|exact Hneq].
  - left; reflexivity.
Qed.

Lemma palindrome_scan_state_112_false_extend : forall s i j,
  palindrome_scan_state_112 s i 0 ->
  i <= j <= Zlength s ->
  palindrome_scan_state_112 s j 0.
Proof.
  intros s i j [Hb [_ [Hmis _]]] Hj.
  split; [lia|].
  split; [intros H; discriminate|].
  split.
  - intros _.
    destruct (Hmis eq_refl) as [k [Hk Hneq]].
    exists k. split; [lia|exact Hneq].
  - left; reflexivity.
Qed.

Lemma row_payload_c_string_112 : forall payload,
  row_payload_z_112 (c_string payload) = payload.
Proof.
  intros payload.
  unfold row_payload_z_112, c_string.
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

Lemma c_string_Zlength_112 : forall payload,
  Zlength (c_string payload) = string_length payload + 1.
Proof.
  intros payload.
  unfold c_string, string_length.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma rows_to_output_reverse_delete_rows_112 : forall s c,
  rows_to_output_112 (reverse_delete_rows_112 s c) =
  (string_of_list_z_112 (filter_not_in_z_112 s c),
   pal_bool_112 (filter_not_in_z_112 s c)).
Proof.
  intros s c.
  unfold rows_to_output_112, reverse_delete_rows_112, bool_row_112,
    row_string_z_112.
  rewrite !row_payload_c_string_112.
  destruct (pal_bool_112 (filter_not_in_z_112 s c)); simpl.
  - unfold true_payload_112.
    repeat rewrite Z.eqb_refl.
    reflexivity.
  - unfold true_payload_112, false_payload_112.
    simpl.
    reflexivity.
Qed.

Lemma problem_112_spec_z_reverse_delete_rows_112 : forall s c,
  valid_reverse_delete_input_112 s c ->
  problem_112_spec_z s c (reverse_delete_rows_112 s c).
Proof.
  intros s c [Hs Hc].
  unfold problem_112_spec_z, problem_112_spec, reverse_delete, del_and_pal_impl.
  rewrite rows_to_output_reverse_delete_rows_112.
  rewrite !list_ascii_of_string_string_of_list_z_112.
  rewrite delete_chars_impl_map_ascii_of_z_112 by assumption.
  rewrite string_of_list_ascii_map_ascii_of_z_112.
  rewrite is_pal_impl_map_ascii_of_z_112.
  - reflexivity.
  - intros x Hx.
    eapply valid_lower_payload_112_In_range; [| exact Hx].
    apply filter_not_in_z_112_valid_lower. exact Hs.
Qed.

Lemma Zlength_reverse_delete_rows_112 : forall s c,
  Zlength (reverse_delete_rows_112 s c) = 2.
Proof.
  intros s c.
  unfold reverse_delete_rows_112.
  rewrite !Zlength_cons, Zlength_nil.
  lia.
Qed.
