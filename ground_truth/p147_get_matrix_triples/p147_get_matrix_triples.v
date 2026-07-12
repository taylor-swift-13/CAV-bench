(* def get_max_triples(n):
You are given a positive integer n. You have to create an integer array a of length n.
For each i (1 ≤ i ≤ n), the value of a[i] = i * i - i + 1.
Return the number of triples (a[i], a[j], a[k]) of a where i < j < k,
and a[i] + a[j] + a[k] is a multiple of 3.

Example :
Input: n = 5
Output: 1
Explanation:
a = [1, 3, 7, 13, 21]
The only valid triple is (1, 7, 13). *)
(* 引入所需的基础库 *)
Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.


(*
 * 定义函数 a(i)，对应于 Python 程序中的 a[i] = i*i - i + 1。
 * 这里的索引 i 是从 1 开始的自然数（nat）。
 * 为了避免自然数减法可能出现的问题，我们使用整数（Z）进行计算。
 *)
Definition a_val (i : nat) : Z :=
  let i_z := Z.of_nat i in
  i_z * i_z - i_z + 1.

(*
 * 定义一个“有效三元组”的属性。
 * 一个三元组 (i, j, k) 是有效的，当且仅当它满足以下所有条件：
 * 1. 索引 i, j, k 满足 1 <= i < j < k <= n。
 * 2. 对应的值 a(i), a(j), a(k) 之和是 3 的倍数。
 *)
Definition is_valid_triple (n i j k : nat) : Prop :=
  (1 <= i)%nat /\ (i < j)%nat /\ (j < k)%nat /\ (k <= n)%nat /\
  (a_val i + a_val j + a_val k) mod 3 = 0.

(* 独立的输入前置条件 *)
Definition problem_147_pre (n : nat) : Prop := (n > 0)%nat.

(*
 * get_max_triples 函数的程序规约。
 * 它通过一阶逻辑描述了输入 n 和输出 output 之间的关系。
 *)
Definition problem_147_spec (n : nat) (output : nat) : Prop :=
  (*
   * 存在一个三元组列表 l，它精确地包含了所有有效的、不重复的三元组，
   * 并且 output 是这个列表的长度。
   *)
  exists (l : list (nat * nat * nat)),
    (* 1. 列表 l 中的每一个元素 (i, j, k) 都必须是一个有效的 instill 三元组。 *)
    (forall ijk, In ijk l ->
      let '(i, j, k) := ijk in is_valid_triple n i j k) /\

    (* 2. 所有有效的 instill 三元组 (i, j, k) 都必须在列表 l 中。 *)
    (forall i j k, is_valid_triple n i j k -> In (i, j, k) l) /\

    (* 3. 列表 l 中没有重复的元素。 *)
    NoDup l /\

    (* 4. 函数的输出 output 必须等于列表 l 的长度。 *)
    output = length l.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Import ListNotations.
Local Open Scope Z_scope.

Definition problem_147_pre_z (n : Z) : Prop :=
  0 <= n /\ problem_147_pre (Z.to_nat n).

Definition problem_147_spec_z (n output : Z) : Prop :=
  0 <= n /\ 0 <= output /\
  problem_147_spec (Z.to_nat n) (Z.to_nat output).

Definition triple_value_147 (i : Z) : Z :=
  i * i - i + 1.

Definition triple_good_bool_147 (i j k : Z) : bool :=
  Z.eqb (Z.rem (triple_value_147 i +
                triple_value_147 j +
                triple_value_147 k) 3) 0.

Definition triple_good_147 (n i j k : Z) : Prop :=
  1 <= i < j /\ j < k /\ k <= n /\
  triple_good_bool_147 i j k = true.

Fixpoint triples_k_aux_147 (n i j : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S fuel' =>
      triples_k_aux_147 n i j fuel' +
      if triple_good_bool_147 i j (j + 1 + Z.of_nat fuel') then 1 else 0
  end.

Definition triples_k_147 (n i j k : Z) : Z :=
  triples_k_aux_147 n i j (Z.to_nat (k - (j + 1))).

Fixpoint triples_j_aux_147 (n i : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S fuel' =>
      triples_j_aux_147 n i fuel' +
      triples_k_147 n i (i + 1 + Z.of_nat fuel') (n + 1)
  end.

Definition triples_j_147 (n i j : Z) : Z :=
  triples_j_aux_147 n i (Z.to_nat (j - (i + 1))).

Fixpoint triples_i_aux_147 (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S fuel' =>
      triples_i_aux_147 n fuel' +
      triples_j_147 n (1 + Z.of_nat fuel') (n + 1)
  end.

Definition triples_i_147 (n i : Z) : Z :=
  triples_i_aux_147 n (Z.to_nat (i - 1)).

Lemma triples_k_nonneg_147 : forall n i j fuel,
  0 <= triples_k_aux_147 n i j fuel.
Proof.
  induction fuel; simpl; intros; try lia.
  destruct (triple_good_bool_147 i j (j + 1 + Z.of_nat fuel)); lia.
Qed.

Lemma triples_k_bound_147 : forall n i j fuel,
  triples_k_aux_147 n i j fuel <= Z.of_nat fuel.
Proof.
  induction fuel; simpl; intros; try lia.
  destruct (triple_good_bool_147 i j (j + 1 + Z.of_nat fuel)); lia.
Qed.

Lemma triples_k_bound_z_147 : forall n i j k,
  triples_k_147 n i j k <= Z.of_nat (Z.to_nat (k - (j + 1))).
Proof.
  intros. unfold triples_k_147. apply triples_k_bound_147.
Qed.

Lemma triples_k_step_raw_147 : forall n i j k,
  j + 1 <= k ->
  triples_k_147 n i j (k + 1) =
  triples_k_147 n i j k +
  if triple_good_bool_147 i j k then 1 else 0.
Proof.
  intros n i j k Hjk.
  unfold triples_k_147.
  replace (Z.to_nat (k + 1 - (j + 1))) with
      (S (Z.to_nat (k - (j + 1)))).
  2:{
    rewrite <- Z2Nat.inj_succ by lia.
    f_equal; lia.
  }
  cbn [triples_k_aux_147].
  replace (j + 1 + Z.of_nat (Z.to_nat (k - (j + 1)))) with k by
    (rewrite Z2Nat.id by lia; lia).
  reflexivity.
Qed.

Lemma triples_k_step_good_147 : forall n i j k,
  j + 1 <= k ->
  triple_good_bool_147 i j k = true ->
  triples_k_147 n i j (k + 1) = triples_k_147 n i j k + 1.
Proof.
  intros. rewrite triples_k_step_raw_147 by lia. rewrite H0. reflexivity.
Qed.

Lemma triples_k_step_bad_147 : forall n i j k,
  j + 1 <= k ->
  triple_good_bool_147 i j k = false ->
  triples_k_147 n i j (k + 1) = triples_k_147 n i j k.
Proof.
  intros. rewrite triples_k_step_raw_147 by lia. rewrite H0. lia.
Qed.

Lemma triples_j_step_147 : forall n i j,
  i + 1 <= j ->
  triples_j_147 n i (j + 1) =
  triples_j_147 n i j + triples_k_147 n i j (n + 1).
Proof.
  intros n i j Hij.
  unfold triples_j_147.
  replace (Z.to_nat (j + 1 - (i + 1))) with
      (S (Z.to_nat (j - (i + 1)))).
  2:{
    rewrite <- Z2Nat.inj_succ by lia.
    f_equal; lia.
  }
  cbn [triples_j_aux_147].
  replace (i + 1 + Z.of_nat (Z.to_nat (j - (i + 1)))) with j by
    (rewrite Z2Nat.id by lia; lia).
  reflexivity.
Qed.

Lemma triples_i_step_147 : forall n i,
  1 <= i ->
  triples_i_147 n (i + 1) =
  triples_i_147 n i + triples_j_147 n i (n + 1).
Proof.
  intros n i Hi.
  unfold triples_i_147.
  replace (Z.to_nat (i + 1 - 1)) with (S (Z.to_nat (i - 1))).
  2:{
    rewrite <- Z2Nat.inj_succ by lia.
    f_equal; lia.
  }
  cbn [triples_i_aux_147].
  replace (1 + Z.of_nat (Z.to_nat (i - 1))) with i by
    (rewrite Z2Nat.id by lia; lia).
  reflexivity.
Qed.

Lemma triples_j_nonneg_147 : forall n i j,
  0 <= triples_j_147 n i j.
Proof.
  intros n i j.
  unfold triples_j_147.
  induction (Z.to_nat (j - (i + 1))); cbn [triples_j_aux_147]; try lia.
  unfold triples_k_147.
  pose proof (triples_k_nonneg_147 n i (i + 1 + Z.of_nat n0)
    (Z.to_nat (n + 1 - (i + 1 + Z.of_nat n0 + 1)))).
  lia.
Qed.

Lemma triples_j_aux_bound_147 : forall n i fuel,
  1 <= i + 1 ->
  i + 1 + Z.of_nat fuel <= n + 1 ->
  n <= 1004 ->
  triples_j_aux_147 n i fuel <= Z.of_nat fuel * 1004.
Proof.
  induction fuel; intros Hi Hfuel Hn; cbn [triples_j_aux_147]; try lia.
  pose proof (IHfuel Hi ltac:(lia) Hn).
  pose proof (triples_k_bound_z_147 n i (i + 1 + Z.of_nat fuel) (n + 1)).
  assert (Z.of_nat (Z.to_nat (n + 1 - (i + 1 + Z.of_nat fuel + 1))) <= 1004).
  {
    rewrite ZifyInst.of_nat_to_nat_eq. lia.
  }
  lia.
Qed.

Lemma triples_j_bound_147 : forall n i j,
  n <= 1004 ->
  1 <= i + 1 ->
  i + 1 <= n + 1 ->
  j <= n + 1 ->
  triples_j_147 n i j <= Z.of_nat (Z.to_nat (j - (i + 1))) * 1004.
Proof.
  intros n i j Hn Hi Hin Hj.
  unfold triples_j_147.
  apply triples_j_aux_bound_147.
  - assumption.
  - rewrite ZifyInst.of_nat_to_nat_eq. lia.
  - assumption.
Qed.

Lemma triples_i_nonneg_147 : forall n i,
  0 <= triples_i_147 n i.
Proof.
  intros n i.
  unfold triples_i_147.
  induction (Z.to_nat (i - 1)); cbn [triples_i_aux_147]; try lia.
  pose proof (triples_j_nonneg_147 n (1 + Z.of_nat n0) (n + 1)).
  lia.
Qed.

Lemma triples_i_aux_bound_147 : forall n fuel,
  1 + Z.of_nat fuel <= n + 1 ->
  n <= 1004 ->
  triples_i_aux_147 n fuel <= Z.of_nat fuel * 1004 * 1004.
Proof.
  induction fuel; intros Hfuel Hn; cbn [triples_i_aux_147]; try lia.
  pose proof (IHfuel ltac:(lia) Hn).
  pose proof (triples_j_bound_147 n (1 + Z.of_nat fuel) (n + 1) Hn ltac:(lia) ltac:(lia) ltac:(lia)).
  assert (Z.of_nat (Z.to_nat (n + 1 - (1 + Z.of_nat fuel + 1))) <= 1004).
  {
    rewrite ZifyInst.of_nat_to_nat_eq. lia.
  }
  lia.
Qed.

Lemma triples_i_bound_147 : forall n i,
  n <= 1004 ->
  1 <= i ->
  i <= n + 1 ->
  triples_i_147 n i <= Z.of_nat (Z.to_nat (i - 1)) * 1004 * 1004.
Proof.
  intros n i Hn Hlow Hi.
  unfold triples_i_147.
  apply triples_i_aux_bound_147.
  - rewrite ZifyInst.of_nat_to_nat_eq. lia.
  - assumption.
Qed.

Lemma triples_partial_bound_147 : forall n i j k,
  1 <= n <= 1004 ->
  1 <= i <= n ->
  i < j <= n ->
  j + 1 <= k <= n + 1 ->
  triples_i_147 n i + triples_j_147 n i j + triples_k_147 n i j k < INT_MAX.
Proof.
  intros n i j k Hn Hi Hj Hk.
  pose proof (triples_i_bound_147 n i ltac:(lia) ltac:(lia) ltac:(lia)).
  pose proof (triples_j_bound_147 n i j ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  pose proof (triples_k_bound_z_147 n i j k).
  assert (Z.of_nat (Z.to_nat (i - 1)) <= 1004).
  { rewrite Z2Nat.id by lia. lia. }
  assert (Z.of_nat (Z.to_nat (j - (i + 1))) <= 1004).
  { rewrite Z2Nat.id by lia. lia. }
  assert (Z.of_nat (Z.to_nat (k - (j + 1))) <= 1004).
  { rewrite Z2Nat.id by lia. lia. }
  lia.
Qed.

Lemma triples_k_nonneg_z_147 : forall n i j k,
  0 <= triples_k_147 n i j k.
Proof.
  intros. unfold triples_k_147. apply triples_k_nonneg_147.
Qed.

Lemma triple_value_range_147 : forall i,
  1 <= i <= 1004 ->
  0 <= triple_value_147 i <= 1007013.
Proof.
  unfold triple_value_147; intros; nia.
Qed.

Lemma triple_sum_range_147 : forall i j k,
  1 <= i <= 1004 ->
  1 <= j <= 1004 ->
  1 <= k <= 1004 ->
  0 <= triple_value_147 i + triple_value_147 j + triple_value_147 k <= 3021039.
Proof.
  intros.
  pose proof (triple_value_range_147 i H).
  pose proof (triple_value_range_147 j H0).
  pose proof (triple_value_range_147 k H1).
  lia.
Qed.

Definition triple_nat_147 := (nat * nat * nat)%type.

Fixpoint triples_k_list_aux_147 (n i j : Z) (fuel : nat) : list triple_nat_147 :=
  match fuel with
  | O => nil
  | S fuel' =>
      let prev := triples_k_list_aux_147 n i j fuel' in
      let k := j + 1 + Z.of_nat fuel' in
      if triple_good_bool_147 i j k
      then prev ++ (Z.to_nat i, Z.to_nat j, Z.to_nat k) :: nil
      else prev
  end.

Fixpoint triples_j_list_aux_147 (n i : Z) (fuel : nat) : list triple_nat_147 :=
  match fuel with
  | O => nil
  | S fuel' =>
      let prev := triples_j_list_aux_147 n i fuel' in
      let j := i + 1 + Z.of_nat fuel' in
      prev ++ triples_k_list_aux_147 n i j (Z.to_nat (n + 1 - (j + 1)))
  end.

Fixpoint triples_i_list_aux_147 (n : Z) (fuel : nat) : list triple_nat_147 :=
  match fuel with
  | O => nil
  | S fuel' =>
      let prev := triples_i_list_aux_147 n fuel' in
      let i := 1 + Z.of_nat fuel' in
      prev ++ triples_j_list_aux_147 n i (Z.to_nat (n + 1 - (i + 1)))
  end.

Definition triples_list_147 (n : Z) : list triple_nat_147 :=
  triples_i_list_aux_147 n (Z.to_nat n).

Lemma a_val_Z_to_nat_147 : forall z,
  0 <= z ->
  a_val (Z.to_nat z) = triple_value_147 z.
Proof.
  intros z Hz.
  unfold a_val, triple_value_147.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.

Lemma triple_good_bool_valid_147 : forall n i j k,
  1 <= i < j ->
  j < k ->
  k <= n ->
  0 <= n ->
  triple_good_bool_147 i j k = true ->
  is_valid_triple (Z.to_nat n) (Z.to_nat i) (Z.to_nat j) (Z.to_nat k).
Proof.
  intros n i j k Hij Hjk Hkn Hn Hgood.
  unfold is_valid_triple.
  repeat split.
  - apply Nat2Z.inj_le. rewrite Z2Nat.id by lia. lia.
  - apply Nat2Z.inj_lt; rewrite !Z2Nat.id by lia; lia.
  - apply Nat2Z.inj_lt; rewrite !Z2Nat.id by lia; lia.
  - apply Nat2Z.inj_le; rewrite !Z2Nat.id by lia; lia.
  - unfold triple_good_bool_147 in Hgood.
    apply Z.eqb_eq in Hgood.
    rewrite !a_val_Z_to_nat_147 by lia.
    rewrite <- Z.rem_mod_nonneg.
    + exact Hgood.
    + unfold triple_value_147; nia.
    + lia.
Qed.

Lemma is_valid_triple_good_bool_147 : forall n i j k,
  is_valid_triple (Z.to_nat n) i j k ->
  0 <= n ->
  triple_good_bool_147 (Z.of_nat i) (Z.of_nat j) (Z.of_nat k) = true.
Proof.
  intros n i j k Hvalid Hn.
  destruct Hvalid as [Hi [Hij [Hjk [Hkn Hmod]]]].
  unfold triple_good_bool_147.
  apply Z.eqb_eq.
  rewrite Z.rem_mod_nonneg.
  - unfold triple_value_147.
    change (Z.of_nat i * Z.of_nat i - Z.of_nat i + 1) with (a_val i).
    change (Z.of_nat j * Z.of_nat j - Z.of_nat j + 1) with (a_val j).
    change (Z.of_nat k * Z.of_nat k - Z.of_nat k + 1) with (a_val k).
    exact Hmod.
  - unfold triple_value_147; nia.
  - lia.
Qed.

Lemma triples_k_list_length_147 : forall n i j fuel,
  Z.of_nat (length (triples_k_list_aux_147 n i j fuel)) =
  triples_k_aux_147 n i j fuel.
Proof.
  intros n i j fuel.
  induction fuel as [|fuel IHfuel].
  - cbn [triples_k_list_aux_147 triples_k_aux_147]. reflexivity.
  - cbn [triples_k_list_aux_147 triples_k_aux_147].
    destruct (triple_good_bool_147 i j (j + 1 + Z.of_nat fuel)); try rewrite length_app; simpl; lia.
Qed.

Lemma triples_j_list_length_147 : forall n i fuel,
  Z.of_nat (length (triples_j_list_aux_147 n i fuel)) =
  triples_j_aux_147 n i fuel.
Proof.
  intros n i fuel.
  induction fuel as [|fuel IHfuel].
  - cbn [triples_j_list_aux_147 triples_j_aux_147]. reflexivity.
  - cbn [triples_j_list_aux_147 triples_j_aux_147].
    rewrite length_app, Nat2Z.inj_add, IHfuel, triples_k_list_length_147.
    reflexivity.
Qed.

Lemma triples_i_list_length_147 : forall n fuel,
  Z.of_nat (length (triples_i_list_aux_147 n fuel)) =
  triples_i_aux_147 n fuel.
Proof.
  intros n fuel.
  induction fuel as [|fuel IHfuel].
  - cbn [triples_i_list_aux_147 triples_i_aux_147]. reflexivity.
  - cbn [triples_i_list_aux_147 triples_i_aux_147].
    rewrite length_app, Nat2Z.inj_add, IHfuel, triples_j_list_length_147.
    reflexivity.
Qed.

Lemma triples_list_length_147 : forall n,
  0 <= n ->
  Z.of_nat (length (triples_list_147 n)) = triples_i_147 n (n + 1).
Proof.
  intros n Hn.
  unfold triples_list_147, triples_i_147.
  replace (Z.to_nat (n + 1 - 1)) with (Z.to_nat n) by (f_equal; lia).
  apply triples_i_list_length_147.
Qed.

Lemma triples_k_list_sound_147 : forall n i j fuel t,
  1 <= i < j ->
  j + Z.of_nat fuel <= n ->
  In t (triples_k_list_aux_147 n i j fuel) ->
  let '(a,b,c) := t in is_valid_triple (Z.to_nat n) a b c.
Proof.
  induction fuel as [|fuel IHfuel]; cbn [triples_k_list_aux_147]; intros t Hij Hfuel Hin; try contradiction.
  destruct (triple_good_bool_147 i j (j + 1 + Z.of_nat fuel)) eqn:Hgood.
  - rewrite in_app_iff in Hin. destruct Hin as [Hin | [Heq | []]].
    + eapply IHfuel; eauto; lia.
    + subst t. apply triple_good_bool_valid_147; try lia; exact Hgood.
  - eapply IHfuel; eauto; lia.
Qed.

Lemma triples_j_list_sound_147 : forall n i fuel t,
  1 <= i ->
  i + Z.of_nat fuel <= n ->
  In t (triples_j_list_aux_147 n i fuel) ->
  let '(a,b,c) := t in is_valid_triple (Z.to_nat n) a b c.
Proof.
  induction fuel as [|fuel IHfuel]; cbn [triples_j_list_aux_147]; intros t Hi Hfuel Hin; try contradiction.
  rewrite in_app_iff in Hin. destruct Hin as [Hin | Hin].
  - eapply IHfuel; eauto; lia.
  - eapply (triples_k_list_sound_147 n i (i + 1 + Z.of_nat fuel)
        (Z.to_nat (n + 1 - (i + 1 + Z.of_nat fuel + 1))) t); eauto; try lia.
Qed.

Lemma triples_i_list_sound_147 : forall n fuel t,
  Z.of_nat fuel <= n ->
  In t (triples_i_list_aux_147 n fuel) ->
  let '(a,b,c) := t in is_valid_triple (Z.to_nat n) a b c.
Proof.
  induction fuel as [|fuel IHfuel]; cbn [triples_i_list_aux_147]; intros t Hfuel Hin; try contradiction.
  rewrite in_app_iff in Hin. destruct Hin as [Hin | Hin].
  - eapply IHfuel; eauto; lia.
  - eapply (triples_j_list_sound_147 n (1 + Z.of_nat fuel)
        (Z.to_nat (n + 1 - (1 + Z.of_nat fuel + 1))) t); eauto; try lia.
Qed.

Lemma triples_list_sound_147 : forall n t,
  0 <= n ->
  In t (triples_list_147 n) ->
  let '(a,b,c) := t in is_valid_triple (Z.to_nat n) a b c.
Proof.
  intros n t Hn Hin.
  unfold triples_list_147 in Hin.
  eapply triples_i_list_sound_147; eauto.
  rewrite Z2Nat.id by lia. lia.
Qed.

Lemma triples_k_list_complete_147 : forall n i j k,
  1 <= i < j ->
  j < k <= n ->
  triple_good_bool_147 i j k = true ->
  In (Z.to_nat i, Z.to_nat j, Z.to_nat k)
     (triples_k_list_aux_147 n i j (Z.to_nat (n - j))).
Proof.
  intros n i j k Hij Hk Hgood.
  remember (Z.to_nat (n - j)) as fuel eqn:Hfuel.
  assert (HfuelZ : Z.of_nat fuel = n - j) by (subst fuel; rewrite Z2Nat.id by lia; lia).
  assert (Hrange : 0 <= k - (j + 1) < Z.of_nat fuel) by lia.
  clear Hfuel HfuelZ.
  revert k Hk Hgood Hrange.
  induction fuel as [|fuel IHfuel]; intros k Hk Hgood Hrange; cbn [triples_k_list_aux_147].
  - lia.
  - destruct (Z.eq_dec (k - (j + 1)) (Z.of_nat fuel)).
    + assert (k = j + 1 + Z.of_nat fuel) by lia. subst k.
      rewrite Hgood. rewrite in_app_iff. right; left.
      f_equal; rewrite Z2Nat.id by lia; reflexivity.
	    + destruct (triple_good_bool_147 i j (j + 1 + Z.of_nat fuel)).
	      * rewrite in_app_iff. left. apply IHfuel; try lia; exact Hgood.
	      * apply IHfuel; try lia; exact Hgood.
Qed.

Lemma triples_j_list_complete_147 : forall n i j k,
  1 <= i < j ->
  j < k <= n ->
  triple_good_bool_147 i j k = true ->
  In (Z.to_nat i, Z.to_nat j, Z.to_nat k)
     (triples_j_list_aux_147 n i (Z.to_nat (n - i))).
Proof.
  intros n i j k Hij Hk Hgood.
  remember (Z.to_nat (n - i)) as fuel eqn:Hfuel.
  assert (HfuelZ : Z.of_nat fuel = n - i) by (subst fuel; rewrite Z2Nat.id by lia; lia).
  assert (Hrange : 0 <= j - (i + 1) < Z.of_nat fuel) by lia.
  clear Hfuel HfuelZ.
  revert j k Hij Hk Hgood Hrange.
  induction fuel as [|fuel IHfuel]; intros j k Hij Hk Hgood Hrange; cbn [triples_j_list_aux_147].
  - lia.
  - destruct (Z.eq_dec (j - (i + 1)) (Z.of_nat fuel)).
    + assert (j = i + 1 + Z.of_nat fuel) by lia. subst j.
      rewrite in_app_iff. right.
      replace (Z.to_nat (n + 1 - (i + 1 + Z.of_nat fuel + 1))) with
        (Z.to_nat (n - (i + 1 + Z.of_nat fuel))) by (f_equal; lia).
      apply triples_k_list_complete_147; try lia; exact Hgood.
    + rewrite in_app_iff. left. apply IHfuel; try lia; exact Hgood.
Qed.

Lemma triples_i_list_complete_147 : forall n i j k,
  1 <= i < j ->
  j < k <= n ->
  triple_good_bool_147 i j k = true ->
  In (Z.to_nat i, Z.to_nat j, Z.to_nat k)
     (triples_i_list_aux_147 n (Z.to_nat n)).
Proof.
  intros n i j k Hij Hk Hgood.
  remember (Z.to_nat n) as fuel eqn:Hfuel.
  assert (HfuelZ : Z.of_nat fuel = n) by (subst fuel; rewrite Z2Nat.id by lia; lia).
  assert (Hrange : 0 <= i - 1 < Z.of_nat fuel) by lia.
  clear Hfuel HfuelZ.
  revert i j k Hij Hk Hgood Hrange.
  induction fuel as [|fuel IHfuel]; intros i j k Hij Hk Hgood Hrange; cbn [triples_i_list_aux_147].
  - lia.
  - destruct (Z.eq_dec (i - 1) (Z.of_nat fuel)).
    + assert (i = 1 + Z.of_nat fuel) by lia. subst i.
      rewrite in_app_iff. right.
      replace (Z.to_nat (n + 1 - (1 + Z.of_nat fuel + 1))) with
        (Z.to_nat (n - (1 + Z.of_nat fuel))) by (f_equal; lia).
      apply triples_j_list_complete_147; try lia; exact Hgood.
    + rewrite in_app_iff. left. apply IHfuel; try lia; exact Hgood.
Qed.

Lemma triples_list_complete_147 : forall n i j k,
  is_valid_triple (Z.to_nat n) i j k ->
  0 <= n ->
  In (i,j,k) (triples_list_147 n).
Proof.
  intros n i j k Hvalid Hn.
  destruct Hvalid as [Hi [Hij [Hjk [Hkn Hmod]]]].
  unfold triples_list_147.
  replace i with (Z.to_nat (Z.of_nat i)) by (rewrite Nat2Z.id; reflexivity).
  replace j with (Z.to_nat (Z.of_nat j)) by (rewrite Nat2Z.id; reflexivity).
  replace k with (Z.to_nat (Z.of_nat k)) by (rewrite Nat2Z.id; reflexivity).
  apply triples_i_list_complete_147.
  - split.
    + lia.
    + apply Nat2Z.inj_lt; exact Hij.
  - split.
    + apply Nat2Z.inj_lt; exact Hjk.
    + apply Nat2Z.inj_le in Hkn. rewrite Z2Nat.id in Hkn by lia. exact Hkn.
  - apply (is_valid_triple_good_bool_147 n i j k); try lia.
    repeat split; try lia; exact Hmod.
Qed.

Lemma triples_k_list_in_range_147 : forall n i j fuel a b c,
  1 <= i < j ->
  In (a,b,c) (triples_k_list_aux_147 n i j fuel) ->
  a = Z.to_nat i /\ b = Z.to_nat j /\ j + 1 <= Z.of_nat c <= j + Z.of_nat fuel.
Proof.
  induction fuel as [|fuel IHfuel]; cbn [triples_k_list_aux_147]; intros a b c Hij Hin; try contradiction.
  destruct (triple_good_bool_147 i j (j + 1 + Z.of_nat fuel)) eqn:Hgood.
  - rewrite in_app_iff in Hin. destruct Hin as [Hin | [Heq | []]].
    + specialize (IHfuel _ _ _ Hij Hin) as [? [? ?]]. repeat split; try assumption; lia.
    + inversion Heq; subst. repeat split; try reflexivity; rewrite Z2Nat.id by lia; lia.
  - specialize (IHfuel _ _ _ Hij Hin) as [? [? ?]]. repeat split; try assumption; lia.
Qed.

Lemma triples_k_list_NoDup_147 : forall n i j fuel,
  1 <= i < j ->
  NoDup (triples_k_list_aux_147 n i j fuel).
Proof.
  intros n i j fuel Hij.
  induction fuel as [|fuel IHfuel].
  - cbn [triples_k_list_aux_147]. constructor.
  - cbn [triples_k_list_aux_147].
    destruct (triple_good_bool_147 i j (j + 1 + Z.of_nat fuel)) eqn:Hgood.
    + apply NoDup_app.
      * apply IHfuel.
      * constructor; [intro H; contradiction|constructor].
      * intros [[a b] c] Hin Hnew.
      destruct Hnew as [Heq | []]. inversion Heq; subst.
      pose proof (triples_k_list_in_range_147 n i j fuel _ _ _ Hij Hin) as [_ [_ Hc]].
      rewrite Z2Nat.id in Hc by lia. lia.
    + apply IHfuel.
Qed.

Lemma triples_j_list_in_range_147 : forall n i fuel a b c,
  1 <= i ->
  In (a,b,c) (triples_j_list_aux_147 n i fuel) ->
  a = Z.to_nat i /\ i + 1 <= Z.of_nat b <= i + Z.of_nat fuel.
Proof.
  induction fuel as [|fuel IHfuel]; cbn [triples_j_list_aux_147]; intros a b c Hi Hin; try contradiction.
  rewrite in_app_iff in Hin. destruct Hin as [Hin | Hin].
  - specialize (IHfuel _ _ _ Hi Hin) as [? ?]. split; try assumption; lia.
  - pose proof (triples_k_list_in_range_147 n i (i + 1 + Z.of_nat fuel)
      (Z.to_nat (n + 1 - (i + 1 + Z.of_nat fuel + 1))) a b c ltac:(lia) Hin)
      as [Ha [Hb Hc]].
    subst b. split; try assumption. rewrite Z2Nat.id by lia. lia.
Qed.

Lemma triples_j_list_NoDup_147 : forall n i fuel,
  1 <= i ->
  i + Z.of_nat fuel <= n ->
  NoDup (triples_j_list_aux_147 n i fuel).
Proof.
  induction fuel as [|fuel IHfuel]; cbn [triples_j_list_aux_147]; intros Hi Hfuel.
  - constructor.
  - apply NoDup_app.
    + apply IHfuel; lia.
    + apply triples_k_list_NoDup_147; lia.
    + intros [[a b] c] Hin1 Hin2.
      pose proof (triples_j_list_in_range_147 n i fuel a b c Hi Hin1) as [_ Hb1].
      pose proof (triples_k_list_in_range_147 n i (i + 1 + Z.of_nat fuel)
        (Z.to_nat (n + 1 - (i + 1 + Z.of_nat fuel + 1))) a b c ltac:(lia) Hin2)
        as [_ [Hb2 _]].
      subst b. rewrite Z2Nat.id in Hb1 by lia. lia.
Qed.

Lemma triples_i_list_in_range_147 : forall n fuel a b c,
  In (a,b,c) (triples_i_list_aux_147 n fuel) ->
  1 <= Z.of_nat a <= Z.of_nat fuel.
Proof.
  induction fuel as [|fuel IHfuel]; cbn [triples_i_list_aux_147]; intros a b c Hin; try contradiction.
  rewrite in_app_iff in Hin. destruct Hin as [Hin | Hin].
  - pose proof (IHfuel _ _ _ Hin). lia.
  - pose proof (triples_j_list_in_range_147 n (1 + Z.of_nat fuel)
      (Z.to_nat (n + 1 - (1 + Z.of_nat fuel + 1))) a b c ltac:(lia) Hin)
      as [Ha _].
    subst a. rewrite Z2Nat.id by lia. lia.
Qed.

Lemma triples_i_list_NoDup_147 : forall n fuel,
  Z.of_nat fuel <= n ->
  NoDup (triples_i_list_aux_147 n fuel).
Proof.
  induction fuel as [|fuel IHfuel]; cbn [triples_i_list_aux_147]; intros Hfuel.
  - constructor.
  - apply NoDup_app.
    + apply IHfuel; lia.
    + apply triples_j_list_NoDup_147; try lia.
    + intros [[a b] c] Hin1 Hin2.
      pose proof (triples_i_list_in_range_147 n fuel a b c Hin1) as Ha1.
      pose proof (triples_j_list_in_range_147 n (1 + Z.of_nat fuel)
        (Z.to_nat (n + 1 - (1 + Z.of_nat fuel + 1))) a b c ltac:(lia) Hin2)
        as [Ha2 _].
      subst a. rewrite Z2Nat.id in Ha1 by lia. lia.
Qed.

Lemma triples_list_NoDup_147 : forall n,
  0 <= n ->
  NoDup (triples_list_147 n).
Proof.
  intros n Hn.
  unfold triples_list_147.
  apply triples_i_list_NoDup_147.
  rewrite Z2Nat.id by lia. lia.
Qed.

Lemma problem_147_spec_z_of_count : forall n,
  1 <= n <= 1004 ->
  problem_147_pre_z n ->
  problem_147_spec_z n (triples_i_147 n (n + 1)).
Proof.
  intros n Hn Hpre.
  unfold problem_147_spec_z.
  split; [lia|].
  split.
  - apply triples_i_nonneg_147.
  - unfold problem_147_spec.
    exists (triples_list_147 n).
    repeat split.
    + intros ijk Hin.
      destruct ijk as [[i j] k].
      apply (triples_list_sound_147 n (i, j, k)); try lia; exact Hin.
    + intros i j k Hvalid.
      apply triples_list_complete_147; try lia; exact Hvalid.
    + apply triples_list_NoDup_147; lia.
    + apply Nat2Z.inj.
      rewrite triples_list_length_147 by lia.
      rewrite Z2Nat.id by apply triples_i_nonneg_147.
      reflexivity.
Qed.
