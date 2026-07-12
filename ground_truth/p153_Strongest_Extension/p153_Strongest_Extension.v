(* def Strongest_Extension(class_name, extensions):
"""You will be given the name of a class (a string) and a list of extensions.
The extensions are to be used to load additional classes to the class. The
strength of the extension is as follows: Let CAP be the number of the uppercase
letters in the extension's name, and let SM be the number of lowercase letters
in the extension's name, the strength is given by the fraction CAP - SM.
You should find the strongest extension and return a string in this
format: ClassName.StrongestExtensionName.
If there are two or more extensions with the same strength, you should
choose the one that comes first in the list.
For example, if you are given "Slices" as the class and a list of the
extensions: ['SErviNGSliCes', 'Cheese', 'StuFfed'] then you should
return 'Slices.SErviNGSliCes' since 'SErviNGSliCes' is the strongest extension
(its strength is -1).
Example:
for Strongest_Extension('my_class', ['AA', 'Be', 'CC']) == 'my_class.AA'
""" *)
(* 引入所需的库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Bool.
Import ListNotations.
Open Scope bool_scope.

(* 定义：检查一个字符是否为大写字母 *)
Definition is_uppercase (c : ascii) : bool :=
  ("A" <=? c)%char && (c <=? "Z")%char.

(* 定义：检查一个字符是否为小写字母 *)
Definition is_lowercase (c : ascii) : bool :=
  ("a" <=? c)%char && (c <=? "z")%char.

(* 辅助函数：计算列表中满足特定谓词的字符数量 *)
Definition count_pred (p : ascii -> bool) (s : list ascii) : nat :=
  length (filter p s).

(* 定义：计算一个扩展名的“力量值” *)
Definition strength (s : string) : Z :=
  let l := list_ascii_of_string s in
  Z.of_nat (count_pred is_uppercase l) - Z.of_nat (count_pred is_lowercase l).

(*
  谓词：is_strongest best exts
  该谓词为真，当且仅当 'best' 是列表 'exts' 中的最强扩展。
  这一定义蕴含了当力量值相同时，选择最先出现的扩展的规则。
*)
Definition is_strongest (best : string) (exts : list string) : Prop :=
  (* 我们可以将列表 'exts' 在 'best' 第一次出现的位置拆分为 'prefix' 和 'post' *)
  exists prefix post,
    exts = prefix ++ best :: post /\
    ~ In best prefix /\ (* 确保这是 'best' 第一次出现 *)
    (
      (* 'best' 的力量值必须严格大于它前面所有元素的力量值 *)
      (forall e, In e prefix -> (strength e < strength best)%Z) /\
      (* 'best' 的力量值必须大于或等于它后面所有元素的力量值 *)
      (forall e, In e post -> (strength e <= strength best)%Z)
    ).

(* 扩展列表必须非空 *)
Definition problem_153_pre (class_name : string) (extensions : list string) : Prop :=
  extensions <> [].


(*
  程序规约：Spec class_name extensions res
  它定义了输入 class_name 和 extensions 与输出 res 之间的关系。
*)
Definition problem_153_spec (class_name : string) (extensions : list string) (res : string) : Prop :=
  match extensions with
  | [] => False (* 对于空的扩展列表，行为是未定义的，因此规约为假 *)
  | _ :: _ => (* 对于非空的扩展列表 *)
      (* 必须存在一个最强的扩展名 'strongest_ext' *)
      exists strongest_ext,
        is_strongest strongest_ext extensions /\
        (* 并且输出 'res' 是 class_name, '.', 和 strongest_ext 的拼接 *)
        res = (class_name ++ "." ++ strongest_ext)%string
  end.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
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

Definition ascii_of_z_153 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_153 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_153 c) (string_of_list_z_153 rest)
  end.

Definition row_payload_z_153 (row : list Z) : list Z :=
  firstn (Z.to_nat (Zlength row - 1)) row.

Definition row_string_z_153 (row : list Z) : string :=
  string_of_list_z_153 (row_payload_z_153 row).

Definition rows_to_strings_z_153 (rows : list (list Z)) : list string :=
  map row_string_z_153 rows.

Definition row_len_z_153 (row : list Z) : Z :=
  string_lib.string_length (row_payload_z_153 row).

Lemma row_payload_c_string_153 : forall s,
  row_payload_z_153 (string_lib.c_string s) = s.
Proof.
  intros s.
  unfold row_payload_z_153, string_lib.c_string.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  change (Z.succ 0) with 1.
  replace (Zlength s + 1 - 1) with (Zlength s) by lia.
  rewrite Zlength_correct, Nat2Z.id.
  rewrite firstn_app.
  rewrite firstn_all.
  rewrite Nat.sub_diag.
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma c_string_payload_prefix_153 : forall s,
  sublist 0 (string_length s) (c_string s) = s.
Proof.
  intros s.
  unfold c_string, string_length.
  apply sublist_app_exact1.
Qed.

Lemma c_string_null_suffix_153 : forall s,
  sublist (string_length s) (string_length s + 1) (c_string s) = cons 0 nil.
Proof.
  intros s.
  unfold c_string, string_length.
  unfold sublist.
  rewrite Zlength_correct.
  rewrite Nat2Z.id.
  replace (Z.to_nat (Z.of_nat (List.length s))) with (List.length s) by lia.
  replace (Z.to_nat (Z.of_nat (List.length s) + 1)) with (S (List.length s)) by lia.
  rewrite firstn_all2 by (rewrite app_length; simpl; lia).
  rewrite skipn_app.
  rewrite skipn_all2 by lia.
  replace (List.length s - List.length s)%nat with 0%nat by lia.
  reflexivity.
Qed.

Definition problem_153_pre_z (class_l : list Z) (rows : list (list Z)) : Prop :=
  problem_153_pre (string_of_list_z_153 class_l) (rows_to_strings_z_153 rows).

Definition problem_153_spec_z
    (class_l : list Z) (rows : list (list Z)) (out_l : list Z) : Prop :=
  problem_153_spec
    (string_of_list_z_153 class_l)
    (rows_to_strings_z_153 rows)
    (string_of_list_z_153 out_l).

Definition is_upper_z_153 (c : Z) : bool :=
  Z.leb 65 c && Z.leb c 90.

Definition is_lower_z_153 (c : Z) : bool :=
  Z.leb 97 c && Z.leb c 122.

Definition char_strength_delta_153 (c : Z) : Z :=
  (if is_upper_z_153 c then 1 else 0) +
  (if is_lower_z_153 c then -1 else 0).

Fixpoint extension_strength_z (s : list Z) : Z :=
  match s with
  | [] => 0
  | c :: rest => char_strength_delta_153 c + extension_strength_z rest
  end.

Definition strength_scan_state_153 (s : list Z) (j strength : Z) : Prop :=
  0 <= j <= string_lib.string_length s /\
  strength = extension_strength_z (sublist 0 j s) /\
  - j <= strength <= j.

Definition best_prefix_state_153
    (rows : list (list Z)) (k best_idx max_strength : Z) : Prop :=
  0 < k <= Zlength rows /\
  0 <= best_idx < k /\
  max_strength =
    extension_strength_z (row_payload_z_153 (Znth best_idx rows nil)) /\
  (forall j,
     0 <= j < k ->
     extension_strength_z (row_payload_z_153 (Znth j rows nil)) <= max_strength) /\
  (forall j,
     0 <= j < k ->
     extension_strength_z (row_payload_z_153 (Znth j rows nil)) = max_strength ->
     best_idx <= j).

Definition output_payload_153 (class_l ext_l : list Z) : list Z :=
  class_l ++ [46] ++ ext_l.

Definition output_len_safe_153
    (class_l : list Z) (rows : list (list Z)) (n : Z) : Prop :=
  forall i,
    0 <= i < n ->
    string_lib.string_length class_l + row_len_z_153 (Znth i rows nil) + 2 < INT_MAX.

Definition rows_well_formed_153 (rows : list (list Z)) (n : Z) : Prop :=
  Zlength rows = n /\
  forall k,
    0 <= k < n ->
    let row := Znth k rows nil in
    let payload := row_payload_z_153 row in
    row = string_lib.c_string payload /\
    string_lib.all_ascii payload /\
    string_lib.no_inner_nul payload /\
    string_lib.string_length payload <= 100 /\
    string_lib.string_length payload < INT_MAX.

Lemma rows_well_formed_153_row : forall rows n k,
  rows_well_formed_153 rows n ->
  0 <= k < n ->
  let row := Znth k rows nil in
  let payload := row_payload_z_153 row in
  row = string_lib.c_string payload /\
  string_lib.valid_string payload /\
  string_lib.string_length payload <= 100 /\
  string_lib.string_length payload < INT_MAX /\
  Zlength row = string_lib.string_length payload + 1.
Proof.
  intros rows n k [Hlen Hwf] Hk row payload.
  specialize (Hwf k Hk).
  destruct Hwf as [Hrow [Hall [Hnul [Hle Hlt]]]].
  split; [exact Hrow|].
  split; [unfold string_lib.valid_string; exact (conj Hall Hnul)|].
  split; [exact Hle|].
  split; [exact Hlt|].
  subst row payload.
  rewrite Hrow at 1.
  unfold string_lib.c_string, string_lib.string_length.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma rows_well_formed_153_char_bound : forall rows n i j,
  rows_well_formed_153 rows n ->
  0 <= i < n ->
  0 <= j < string_lib.string_length (row_payload_z_153 (Znth i rows nil)) ->
  0 <= Znth j (Znth i rows nil) 0 <= 127.
Proof.
  intros rows n i j Hwf Hi Hj.
  pose proof (rows_well_formed_153_row rows n i Hwf Hi) as Hrow.
  destruct Hrow as [Hrow_eq Hrow_tail].
  destruct Hrow_tail as [Hvalid Hrow_tail].
  destruct Hrow_tail as [Hle Hrow_tail].
  destruct Hrow_tail as [Hlt Hrow_len].
  rewrite Hrow_eq.
  rewrite string_lib.c_string_Znth_inside by exact Hj.
  unfold string_lib.valid_string in Hvalid.
  destruct Hvalid as (Hall & Hnul).
  apply Hall.
  unfold string_lib.string_length in Hj.
  lia.
Qed.

Lemma strength_scan_state_153_initial : forall s,
  strength_scan_state_153 s 0 0.
Proof.
  intros s.
  unfold strength_scan_state_153.
  split.
  - unfold string_lib.string_length. rewrite Zlength_correct. lia.
  - split.
    + unfold sublist. reflexivity.
    + lia.
Qed.

Lemma extension_strength_z_app_single : forall s c,
  extension_strength_z (s ++ [c]) =
  extension_strength_z s + char_strength_delta_153 c.
Proof.
  induction s as [|x xs IH]; intros c; simpl.
  - lia.
  - rewrite IH. lia.
Qed.

Lemma char_strength_delta_153_bound : forall c,
  -1 <= char_strength_delta_153 c <= 1.
Proof.
  intros c.
  unfold char_strength_delta_153.
  destruct (is_upper_z_153 c); destruct (is_lower_z_153 c); lia.
Qed.

Lemma char_strength_delta_153_low : forall c,
  c < 65 ->
  char_strength_delta_153 c = 0.
Proof.
  intros c Hc.
  unfold char_strength_delta_153, is_upper_z_153, is_lower_z_153.
  destruct (Z.leb 65 c) eqn:H65; [apply Z.leb_le in H65; lia|].
  destruct (Z.leb 97 c) eqn:H97; [apply Z.leb_le in H97; lia|].
  reflexivity.
Qed.

Lemma char_strength_delta_153_mid : forall c,
  90 < c < 97 ->
  char_strength_delta_153 c = 0.
Proof.
  intros c Hc.
  unfold char_strength_delta_153, is_upper_z_153, is_lower_z_153.
  destruct (Z.leb 65 c) eqn:H65; [|apply Z.leb_gt in H65; lia].
  destruct (Z.leb c 90) eqn:H90; [apply Z.leb_le in H90; lia|].
  destruct (Z.leb 97 c) eqn:H97; [apply Z.leb_le in H97; lia|].
  reflexivity.
Qed.

Lemma char_strength_delta_153_upper : forall c,
  65 <= c <= 90 ->
  char_strength_delta_153 c = 1.
Proof.
  intros c Hc.
  unfold char_strength_delta_153, is_upper_z_153, is_lower_z_153.
  destruct (Z.leb 65 c) eqn:H65; [|apply Z.leb_gt in H65; lia].
  destruct (Z.leb c 90) eqn:H90; [|apply Z.leb_gt in H90; lia].
  destruct (Z.leb 97 c) eqn:H97; [apply Z.leb_le in H97; lia|].
  reflexivity.
Qed.

Lemma char_strength_delta_153_lower : forall c,
  97 <= c <= 122 ->
  char_strength_delta_153 c = -1.
Proof.
  intros c Hc.
  unfold char_strength_delta_153, is_upper_z_153, is_lower_z_153.
  destruct (Z.leb 65 c) eqn:H65; [|apply Z.leb_gt in H65; lia].
  destruct (Z.leb c 90) eqn:H90; [apply Z.leb_le in H90; lia|].
  destruct (Z.leb 97 c) eqn:H97; [|apply Z.leb_gt in H97; lia].
  destruct (Z.leb c 122) eqn:H122; [|apply Z.leb_gt in H122; lia].
  reflexivity.
Qed.

Lemma char_strength_delta_153_high : forall c,
  122 < c ->
  char_strength_delta_153 c = 0.
Proof.
  intros c Hc.
  unfold char_strength_delta_153, is_upper_z_153, is_lower_z_153.
  destruct (Z.leb 65 c) eqn:H65; [|apply Z.leb_gt in H65; lia].
  destruct (Z.leb c 90) eqn:H90; [apply Z.leb_le in H90; lia|].
  destruct (Z.leb 97 c) eqn:H97; [|apply Z.leb_gt in H97; lia].
  destruct (Z.leb c 122) eqn:H122; [apply Z.leb_le in H122; lia|].
  reflexivity.
Qed.

Lemma strength_scan_state_153_step : forall s j strength c,
  0 <= j < string_lib.string_length s ->
  c = Znth j s 0 ->
  strength_scan_state_153 s j strength ->
  strength_scan_state_153 s (j + 1) (strength + char_strength_delta_153 c).
Proof.
  intros s j strength c Hj Hc [Hbounds [Hstrength Hrange]].
  unfold strength_scan_state_153.
  split; [lia|].
  split.
  - rewrite Hstrength.
    unfold string_lib.string_length in Hj.
    rewrite (sublist_split 0 (j + 1) j s) by lia.
    replace (sublist j (j + 1) s) with [Znth j s 0]
      by (symmetry; apply sublist_single; lia).
    rewrite extension_strength_z_app_single.
    subst c.
    lia.
  - pose proof (char_strength_delta_153_bound c).
    lia.
Qed.

Lemma strength_scan_state_153_step_eq : forall s j strength c new_strength,
  0 <= j < string_lib.string_length s ->
  c = Znth j s 0 ->
  strength_scan_state_153 s j strength ->
  new_strength = strength + char_strength_delta_153 c ->
  strength_scan_state_153 s (j + 1) new_strength.
Proof.
  intros s j strength c new_strength Hj Hc Hstate Hnew.
  subst new_strength.
  eapply strength_scan_state_153_step; eauto.
Qed.

Lemma strength_scan_state_153_finish : forall s j strength,
  j >= string_lib.string_length s ->
  strength_scan_state_153 s j strength ->
  strength = extension_strength_z s.
Proof.
  intros s j strength Hj [Hbounds [Hstrength _]].
  rewrite Hstrength.
  replace j with (string_lib.string_length s) by lia.
  unfold string_lib.string_length.
  rewrite sublist_self by reflexivity.
  reflexivity.
Qed.

Lemma best_prefix_state_153_initial : forall rows n,
  rows_well_formed_153 rows n ->
  0 < n ->
  best_prefix_state_153 rows 1 0
    (extension_strength_z (row_payload_z_153 (Znth 0 rows nil))).
Proof.
  intros rows n [Hlen Hwf] Hn.
  unfold best_prefix_state_153.
  rewrite Hlen.
  split; [lia|].
  split; [lia|].
  split; [reflexivity|].
  split.
  - intros j Hj.
    assert (j = 0) by lia.
    subst j.
    lia.
  - intros j Hj _.
    lia.
Qed.

Lemma best_prefix_state_153_step_keep : forall rows k best_idx max_strength cur_strength,
  best_prefix_state_153 rows k best_idx max_strength ->
  k < Zlength rows ->
  cur_strength = extension_strength_z (row_payload_z_153 (Znth k rows nil)) ->
  cur_strength <= max_strength ->
  best_prefix_state_153 rows (k + 1) best_idx max_strength.
Proof.
  intros rows k best_idx max_strength cur_strength Hstate Hk Hcur Hle.
  destruct Hstate as [Hbounds [Hbest [Hmax [Hall Hearliest]]]].
  unfold best_prefix_state_153.
  repeat split; try lia; auto.
  - intros j Hj.
    destruct (Z.eq_dec j k) as [->|Hneq].
    + lia.
    + apply Hall. lia.
  - intros j Hj Heq.
    destruct (Z.eq_dec j k) as [->|Hneq].
    + subst cur_strength.
      rewrite Heq in Hle.
      lia.
    + apply Hearliest; lia.
Qed.

Lemma best_prefix_state_153_step_update : forall rows k best_idx max_strength cur_strength,
  best_prefix_state_153 rows k best_idx max_strength ->
  k < Zlength rows ->
  cur_strength = extension_strength_z (row_payload_z_153 (Znth k rows nil)) ->
  max_strength < cur_strength ->
  best_prefix_state_153 rows (k + 1) k cur_strength.
Proof.
  intros rows k best_idx max_strength cur_strength Hstate Hk Hcur Hgt.
  destruct Hstate as [Hbounds [Hbest [Hmax [Hall Hearliest]]]].
  unfold best_prefix_state_153.
  repeat split; try lia; auto.
  - intros j Hj.
    destruct (Z.eq_dec j k) as [->|Hneq].
    + lia.
    + specialize (Hall j ltac:(lia)). lia.
  - intros j Hj Heq.
    destruct (Z.eq_dec j k) as [->|Hneq]; [lia|].
    specialize (Hall j ltac:(lia)).
    lia.
Qed.

Lemma string_of_list_z_153_app : forall a b,
  string_of_list_z_153 (a ++ b) =
  String.append (string_of_list_z_153 a) (string_of_list_z_153 b).
Proof.
  induction a as [|x xs IH]; intros b; simpl; auto.
  rewrite IH. reflexivity.
Qed.

Lemma ascii_of_z_153_46 :
  ascii_of_z_153 46 = "."%char.
Proof.
  reflexivity.
Qed.

Lemma list_ascii_of_string_string_of_list_z_153 : forall l,
  list_ascii_of_string (string_of_list_z_153 l) = map ascii_of_z_153 l.
Proof.
  induction l; simpl; congruence.
Qed.

Lemma output_payload_string_153 : forall class_l ext_l,
  string_of_list_z_153 (output_payload_153 class_l ext_l) =
  (string_of_list_z_153 class_l ++ "." ++ string_of_list_z_153 ext_l)%string.
Proof.
  intros class_l ext_l.
  unfold output_payload_153.
  rewrite !string_of_list_z_153_app.
  simpl.
  rewrite ascii_of_z_153_46.
  reflexivity.
Qed.

Lemma N_of_ascii_of_z_153 : forall z,
  0 <= z < 256 ->
  N_of_ascii (ascii_of_z_153 z) = Z.to_N z.
Proof.
  intros z Hz.
  unfold ascii_of_z_153.
  apply Nnat.N2Nat.inj.
  change (nat_of_ascii (ascii_of_nat (Z.to_nat z)) = N.to_nat (Z.to_N z)).
  rewrite nat_ascii_embedding by lia.
  symmetry.
  apply Z_N_nat.
Qed.

Lemma ascii_leb_z_153 : forall a b,
  0 <= a < 256 ->
  0 <= b < 256 ->
  (ascii_of_z_153 a <=? ascii_of_z_153 b)%char = true <-> a <= b.
Proof.
  intros a b Ha Hb.
  split; intro H.
  - unfold Ascii.leb, Ascii.compare in H.
    rewrite !N_of_ascii_of_z_153 in H by lia.
    destruct (Z_le_gt_dec a b) as [|Hgt]; [lia|].
    assert ((Z.to_N a ?= Z.to_N b)%N = Gt)
      by (apply N.compare_gt_iff; lia).
    rewrite H0 in H.
    discriminate.
  - unfold Ascii.leb, Ascii.compare.
    rewrite !N_of_ascii_of_z_153 by lia.
    destruct (Z.to_N a ?= Z.to_N b)%N eqn:Hcmp; auto.
    apply N.compare_gt_iff in Hcmp.
    lia.
Qed.

Lemma is_uppercase_of_z_153 : forall c,
  0 <= c <= 127 ->
  is_uppercase (ascii_of_z_153 c) = is_upper_z_153 c.
Proof.
  intros c Hc.
  unfold is_uppercase, is_upper_z_153.
  change "A"%char with (ascii_of_z_153 65).
  change "Z"%char with (ascii_of_z_153 90).
  destruct (Z.leb_spec 65 c) as [H65|H65];
    destruct (Z.leb_spec c 90) as [H90|H90]; simpl.
  - assert ((ascii_of_z_153 65 <=? ascii_of_z_153 c)%char = true)
      by (apply ascii_leb_z_153; lia).
    assert ((ascii_of_z_153 c <=? ascii_of_z_153 90)%char = true)
      by (apply ascii_leb_z_153; lia).
    rewrite H, H0. reflexivity.
  - assert ((ascii_of_z_153 c <=? ascii_of_z_153 90)%char = false).
    { destruct (ascii_of_z_153 c <=? ascii_of_z_153 90)%char eqn:Hcmp; auto.
      apply ascii_leb_z_153 in Hcmp; lia. }
    rewrite H. destruct (ascii_of_z_153 65 <=? ascii_of_z_153 c)%char; reflexivity.
  - assert ((ascii_of_z_153 65 <=? ascii_of_z_153 c)%char = false).
    { destruct (ascii_of_z_153 65 <=? ascii_of_z_153 c)%char eqn:Hcmp; auto.
      apply ascii_leb_z_153 in Hcmp; lia. }
    rewrite H. reflexivity.
  - assert ((ascii_of_z_153 65 <=? ascii_of_z_153 c)%char = false).
    { destruct (ascii_of_z_153 65 <=? ascii_of_z_153 c)%char eqn:Hcmp; auto.
      apply ascii_leb_z_153 in Hcmp; lia. }
    rewrite H. reflexivity.
Qed.

Lemma is_lowercase_of_z_153 : forall c,
  0 <= c <= 127 ->
  is_lowercase (ascii_of_z_153 c) = is_lower_z_153 c.
Proof.
  intros c Hc.
  unfold is_lowercase, is_lower_z_153.
  change "a"%char with (ascii_of_z_153 97).
  change "z"%char with (ascii_of_z_153 122).
  destruct (Z.leb_spec 97 c) as [H97|H97];
    destruct (Z.leb_spec c 122) as [H122|H122]; simpl.
  - assert ((ascii_of_z_153 97 <=? ascii_of_z_153 c)%char = true)
      by (apply ascii_leb_z_153; lia).
    assert ((ascii_of_z_153 c <=? ascii_of_z_153 122)%char = true)
      by (apply ascii_leb_z_153; lia).
    rewrite H, H0. reflexivity.
  - assert ((ascii_of_z_153 c <=? ascii_of_z_153 122)%char = false).
    { destruct (ascii_of_z_153 c <=? ascii_of_z_153 122)%char eqn:Hcmp; auto.
      apply ascii_leb_z_153 in Hcmp; lia. }
    rewrite H. destruct (ascii_of_z_153 97 <=? ascii_of_z_153 c)%char; reflexivity.
  - assert ((ascii_of_z_153 97 <=? ascii_of_z_153 c)%char = false).
    { destruct (ascii_of_z_153 97 <=? ascii_of_z_153 c)%char eqn:Hcmp; auto.
      apply ascii_leb_z_153 in Hcmp; lia. }
    rewrite H. reflexivity.
  - assert ((ascii_of_z_153 97 <=? ascii_of_z_153 c)%char = false).
    { destruct (ascii_of_z_153 97 <=? ascii_of_z_153 c)%char eqn:Hcmp; auto.
      apply ascii_leb_z_153 in Hcmp; lia. }
    rewrite H. reflexivity.
Qed.

Definition ascii_strength_delta_153 (c : ascii) : Z :=
  (if is_uppercase c then 1 else 0) +
  (if is_lowercase c then -1 else 0).

Lemma strength_string_cons_153 : forall c s,
  strength (String c s) = ascii_strength_delta_153 c + strength s.
Proof.
  intros c s.
  unfold strength, ascii_strength_delta_153, count_pred.
  cbn [list_ascii_of_string filter length].
  destruct (is_uppercase c); destruct (is_lowercase c);
    repeat match goal with
    | |- context[Datatypes.length (?x :: ?xs)] =>
        change (Datatypes.length (x :: xs)) with (S (Datatypes.length xs))
    end;
    rewrite ?Nat2Z.inj_succ; lia.
Qed.

Lemma char_strength_delta_153_spec : forall c,
  0 <= c <= 127 ->
  char_strength_delta_153 c = ascii_strength_delta_153 (ascii_of_z_153 c).
Proof.
  intros c Hc.
  unfold char_strength_delta_153, ascii_strength_delta_153.
  rewrite is_uppercase_of_z_153 by lia.
  rewrite is_lowercase_of_z_153 by lia.
  reflexivity.
Qed.

Lemma all_ascii_cons_153 : forall c rest,
  string_lib.all_ascii (c :: rest) ->
  0 <= c <= 127 /\ string_lib.all_ascii rest.
Proof.
  intros c rest Hall.
  split.
  - specialize (Hall 0).
    unfold string_lib.string_length in Hall.
    replace (Znth 0 (c :: rest) 0) with c in Hall by reflexivity.
    apply Hall.
    rewrite Zlength_cons.
    pose proof (Zlength_nonneg rest).
    lia.
  - intros i Hi.
    specialize (Hall (i + 1)).
    unfold string_lib.string_length in *.
    rewrite Znth_cons in Hall by lia.
    replace (i + 1 - 1) with i in Hall by lia.
    apply Hall.
    rewrite Zlength_cons.
    pose proof (Zlength_nonneg rest).
    lia.
Qed.

Lemma extension_strength_z_spec_strength : forall s,
  string_lib.all_ascii s ->
  extension_strength_z s = strength (string_of_list_z_153 s).
Proof.
  induction s as [|c rest IH]; intros Hall.
  - reflexivity.
  - simpl.
    rewrite strength_string_cons_153.
    pose proof (all_ascii_cons_153 c rest Hall) as [Hc Hrest].
    rewrite IH by exact Hrest.
    rewrite char_strength_delta_153_spec by exact Hc.
    reflexivity.
Qed.

Lemma rows_well_formed_153_row_strength : forall rows n i,
  rows_well_formed_153 rows n ->
  0 <= i < n ->
  extension_strength_z (row_payload_z_153 (Znth i rows nil)) =
  strength (row_string_z_153 (Znth i rows nil)).
Proof.
  intros rows n i Hwf Hi.
  pose proof (rows_well_formed_153_row rows n i Hwf Hi) as Hrow.
  destruct Hrow as [_ [Hvalid _]].
  unfold row_string_z_153.
  apply extension_strength_z_spec_strength.
  destruct Hvalid as [Hall _].
  exact Hall.
Qed.

Lemma rows_to_strings_z_153_split_best : forall rows n best_idx,
  Zlength rows = n ->
  0 <= best_idx < n ->
  rows_to_strings_z_153 rows =
    map row_string_z_153 (firstn (Z.to_nat best_idx) rows) ++
    row_string_z_153 (Znth best_idx rows nil) ::
    map row_string_z_153 (skipn (S (Z.to_nat best_idx)) rows).
Proof.
  intros rows n best_idx Hlen Hbest.
  unfold rows_to_strings_z_153.
  change (row_string_z_153 (Znth best_idx rows nil) ::
          map row_string_z_153 (skipn (S (Z.to_nat best_idx)) rows))
    with (map row_string_z_153
            (Znth best_idx rows nil :: skipn (S (Z.to_nat best_idx)) rows)).
  rewrite <- map_app.
  apply f_equal.
  symmetry.
  apply firstn_skipn_middle.
  apply nth_error_nth'.
  apply Nat2Z.inj_lt.
  rewrite Z2Nat.id by lia.
  rewrite <- Zlength_correct.
  lia.
Qed.

Lemma best_prefix_state_153_problem_spec : forall class_l rows n best_idx max_strength,
  rows_well_formed_153 rows n ->
  problem_153_pre_z class_l rows ->
  best_prefix_state_153 rows n best_idx max_strength ->
  problem_153_spec_z
    class_l rows
    (output_payload_153 class_l (row_payload_z_153 (Znth best_idx rows nil))).
Proof.
  intros class_l rows n best_idx max_strength Hwf _ Hbest.
  destruct Hwf as [Hlen Hwf_rows].
  destruct Hbest as [Hk [Hbest_range [Hmax [Hall Hearliest]]]].
  assert (Hbest_n : 0 <= best_idx < n) by lia.
  assert (Hn_pos : 0 < n) by lia.
  pose proof (rows_to_strings_z_153_split_best rows n best_idx Hlen Hbest_n)
    as Hsplit.
  set (best_row := Znth best_idx rows nil).
  set (best_s := row_string_z_153 best_row).
  set (prefix := map row_string_z_153 (firstn (Z.to_nat best_idx) rows)).
  set (post := map row_string_z_153 (skipn (S (Z.to_nat best_idx)) rows)).
  assert (Hbest_strength :
    extension_strength_z (row_payload_z_153 best_row) = strength best_s).
  { subst best_row best_s.
    apply rows_well_formed_153_row_strength with (n := n); [split; auto|lia]. }
  change (Znth best_idx rows nil) with best_row in Hmax.
  assert (Hprefix_lt : forall e, In e prefix -> (strength e < strength best_s)%Z).
  {
    intros e Hin.
    subst prefix.
    apply in_map_iff in Hin.
    destruct Hin as [row [He Hrow_in]].
    apply In_nth with (d := @nil Z) in Hrow_in.
    destruct Hrow_in as [m [Hm Hnth]].
    rewrite firstn_length in Hm.
    rewrite Nat.min_glb_lt_iff in Hm.
    destruct Hm as [Hm_best Hm_rows].
    assert (Hm_best_nat : (m < Z.to_nat best_idx)%nat) by exact Hm_best.
    assert (Hj_range : 0 <= Z.of_nat m < n)
      by (rewrite Zlength_correct in Hlen; apply Nat2Z.inj_lt in Hm_rows; lia).
    assert (Hj_best : Z.of_nat m < best_idx)
      by (apply Nat2Z.inj_lt in Hm_best; rewrite Z2Nat.id in Hm_best by lia; lia).
    rewrite nth_firstn in Hnth by exact Hm_best_nat.
    assert (Hrow_eq : row = Znth (Z.of_nat m) rows nil)
      by (subst row; unfold Znth; rewrite Nat2Z.id; reflexivity).
    subst e.
    rewrite Hrow_eq.
    pose proof (Hall (Z.of_nat m) ltac:(lia)) as Hle.
    pose proof (Hearliest (Z.of_nat m) ltac:(lia)) as Hear.
    pose proof (rows_well_formed_153_row_strength rows n (Z.of_nat m)
      (conj Hlen Hwf_rows) Hj_range) as Hrow_strength.
    rewrite Hrow_strength in Hle.
    rewrite Hbest_strength in Hmax.
    rewrite Hmax in Hle.
    assert (Hstrict :
      strength (row_string_z_153 (Znth (Z.of_nat m) rows nil)) <
      strength best_s) by (
      assert (Hneq :
        strength (row_string_z_153 (Znth (Z.of_nat m) rows nil)) <>
        strength best_s) by
        (intro Heq_strength;
        assert (extension_strength_z (row_payload_z_153 (Znth (Z.of_nat m) rows nil)) =
                max_strength) as Heq_ext by (rewrite Hrow_strength; rewrite Hmax; lia);
        specialize (Hear Heq_ext);
        lia);
      lia).
    exact Hstrict.
  }
  assert (Hpost_le : forall e, In e post -> (strength e <= strength best_s)%Z).
  {
    intros e Hin.
    subst post.
    apply in_map_iff in Hin.
    destruct Hin as [row [He Hrow_in]].
    apply In_nth with (d := @nil Z) in Hrow_in.
    destruct Hrow_in as [m [Hm Hnth]].
    set (j := best_idx + 1 + Z.of_nat m).
    assert (Hj_range : 0 <= j < n).
    {
      subst j.
      rewrite skipn_length in Hm.
      rewrite Zlength_correct in Hlen.
      apply Nat2Z.inj_lt in Hm.
      rewrite Nat2Z.inj_sub in Hm by
        (apply Nat2Z.inj_le; rewrite Nat2Z.inj_succ, Z2Nat.id by lia; lia).
      rewrite Nat2Z.inj_succ in Hm.
      rewrite Z2Nat.id in Hm by lia.
      lia.
    }
    assert (Hrow_eq : row = Znth j rows nil).
    {
      subst j.
      rewrite nth_skipn in Hnth.
      unfold Znth.
      rewrite <- Hnth.
      f_equal.
      rewrite Z2Nat.inj_add by lia.
      replace (Z.to_nat (best_idx + 1)) with (S (Z.to_nat best_idx)) by
        (apply Nat2Z.inj; rewrite Nat2Z.inj_succ; rewrite !Z2Nat.id by lia; lia).
      lia.
    }
    subst e.
    rewrite Hrow_eq.
    pose proof (Hall j ltac:(lia)) as Hle.
    pose proof (rows_well_formed_153_row_strength rows n j
      (conj Hlen Hwf_rows) Hj_range) as Hrow_strength.
    rewrite Hrow_strength in Hle.
    rewrite Hbest_strength in Hmax.
    rewrite Hmax in Hle.
    exact Hle.
  }
  unfold problem_153_spec_z, problem_153_spec.
  rewrite Hsplit.
  change (map row_string_z_153 (firstn (Z.to_nat best_idx) rows)) with prefix.
  change (map row_string_z_153 (skipn (S (Z.to_nat best_idx)) rows)) with post.
  destruct prefix as [|p prefix']; simpl.
  - exists best_s.
    split.
    + unfold is_strongest.
      exists [], post.
      split; [reflexivity|].
      split; [intro Hin; inversion Hin|].
      split.
      * intros e Hin. inversion Hin.
      * exact Hpost_le.
    + rewrite output_payload_string_153.
      subst best_s best_row.
      reflexivity.
  - exists best_s.
    split.
    + unfold is_strongest.
      exists (p :: prefix'), post.
      split; [reflexivity|].
      split.
      * intro Hin.
        pose proof (Hprefix_lt best_s Hin).
        lia.
      * split; [exact Hprefix_lt|exact Hpost_le].
    + rewrite output_payload_string_153.
      subst best_s best_row.
      reflexivity.
Qed.
