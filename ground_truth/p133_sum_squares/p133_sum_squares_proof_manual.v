Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.ground_truth_p133_sum_squares Require Import p133_sum_squares_goal.
From SimpleC.EE.CAV.ground_truth_p133_sum_squares Require Import p133_sum_squares_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p133_sum_squares.
Local Open Scope sac.
Import ListNotations.

Lemma firstn_succ_nth_133 : forall (n : nat) (xs : list Z),
  (n < length xs)%nat ->
  firstn (S n) xs = List.app (firstn n xs) [nth n xs 0].
Proof.
  induction n as [|n IH]; intros xs Hlt.
  - destruct xs; [simpl in Hlt; lia | reflexivity].
  - destruct xs as [|x xs]; [simpl in Hlt; lia |].
    simpl. f_equal. apply IH. simpl in Hlt. lia.
Qed.

Lemma firstn_step_133 : forall (xs : list Z) i,
  0 <= i < Zlength xs ->
  firstn (Z.to_nat (i + 1)) xs =
  List.app (firstn (Z.to_nat i) xs) [Znth i xs 0].
Proof.
  intros xs i Hi.
  assert (Hnat : Z.to_nat (i + 1) = S (Z.to_nat i)).
  { rewrite Z2Nat.inj_add by lia. change (Z.to_nat i + 1 = S (Z.to_nat i))%nat. lia. }
  rewrite Hnat, firstn_succ_nth_133.
  - unfold Znth. reflexivity.
  - apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct. lia.
Qed.

Lemma sum_squares_app_133 : forall ns ds n d,
  length ns = length ds ->
  sum_squares_ratio_133 (List.app ns [n]) (List.app ds [d]) =
  sum_squares_ratio_133 ns ds +
  ceil_ratio_133 n d * ceil_ratio_133 n d.
Proof.
  induction ns as [|x ns IH]; intros ds n d Hlen.
  - destruct ds; [cbn [List.app sum_squares_ratio_133]; ring |
                  simpl in Hlen; discriminate].
  - destruct ds as [|y ds]; [simpl in Hlen; discriminate |].
    simpl in Hlen.
    change
      (ceil_ratio_133 x y * ceil_ratio_133 x y +
         sum_squares_ratio_133 (List.app ns [n]) (List.app ds [d]) =
       ceil_ratio_133 x y * ceil_ratio_133 x y +
         sum_squares_ratio_133 ns ds +
         ceil_ratio_133 n d * ceil_ratio_133 n d).
    rewrite IH by lia. ring.
Qed.

Lemma prefix_step_133 : forall nums dens i sum,
  Zlength nums = Zlength dens ->
  0 <= i < Zlength nums ->
  problem_133_prefix_z nums dens i sum ->
  problem_133_prefix_z nums dens (i + 1)
    (sum + ceil_ratio_133 (Znth i nums 0) (Znth i dens 0) *
           ceil_ratio_133 (Znth i nums 0) (Znth i dens 0)).
Proof.
  intros nums dens i sum Hlen Hi Hprefix.
  unfold problem_133_prefix_z in *.
  rewrite firstn_step_133 by exact Hi.
  rewrite firstn_step_133.
  2: { rewrite <- Hlen. exact Hi. }
  rewrite sum_squares_app_133.
  2: {
    rewrite !firstn_length.
    assert (Hnat : length nums = length dens).
    { apply Nat2Z.inj. rewrite <- !Zlength_correct. exact Hlen. }
    rewrite Hnat. reflexivity.
  }
  rewrite <- Hprefix. reflexivity.
Qed.

Lemma prefix_final_133 : forall nums dens i sum,
  i = Zlength nums -> Zlength nums = Zlength dens ->
  problem_133_prefix_z nums dens i sum ->
  problem_133_spec_z nums dens sum.
Proof.
  intros nums dens i sum Hi Hlen Hprefix.
  unfold problem_133_spec_z.
  change
    (sum = sum_squares_ratio_133
       (firstn (Z.to_nat i) nums) (firstn (Z.to_nat i) dens))
    in Hprefix.
  rewrite Hprefix.
  assert (Hnums : Z.to_nat i = length nums).
  { apply Nat2Z.inj. rewrite Z2Nat.id by (rewrite Hi; apply Zlength_nonneg).
    rewrite <- Zlength_correct. exact Hi. }
  assert (Hnatlen : length nums = length dens).
  { apply Nat2Z.inj. rewrite <- !Zlength_correct. exact Hlen. }
  rewrite Hnums, firstn_all, Hnatlen, firstn_all.
  reflexivity.
Qed.

Ltac get_pre_133 Hpre i :=
  destruct Hpre as [_ Hbound];
  specialize (Hbound i ltac:(lia));
  cbn zeta in Hbound;
  destruct Hbound as [? [? [? [? ?]]]].

Ltac solve_div_safety_133 name :=
  unfold name; left; intros; Intros; entailer!;
  match goal with
  | Hpre : problem_133_pre_z ?nums ?dens,
    Hlt : ?idx < _ |- _ => get_pre_133 Hpre idx; lia
  end.

Lemma proof_of_sum_squares_safety_wit_3 : sum_squares_safety_wit_3.
Proof. solve_div_safety_133 sum_squares_safety_wit_3. Qed.

Lemma proof_of_sum_squares_safety_wit_4 : sum_squares_safety_wit_4.
Proof. solve_div_safety_133 sum_squares_safety_wit_4. Qed.

Lemma proof_of_sum_squares_safety_wit_6 : sum_squares_safety_wit_6.
Proof.
  unfold sum_squares_safety_wit_6; left; intros; Intros; entailer!;
  get_pre_133 PreH8 i;
  unfold ceil_ratio_133 in *; cbv zeta in *;
  destruct (0 <? Z.rem (Znth i nums 0) (Znth i dens 0)) eqn:E;
  try apply Z.ltb_lt in E; try apply Z.ltb_ge in E; lia.
Qed.

Ltac solve_branch_bound_133 name :=
  unfold name; left; intros; Intros; entailer!;
  match goal with
  | Hpre : problem_133_pre_z ?nums ?dens,
    Hprefix : problem_133_prefix_z ?nums ?dens ?idx ?sum,
    Hlt : ?idx < _ |- _ =>
      get_pre_133 Hpre idx;
      unfold ceil_ratio_133 in *; cbv zeta in *;
      first [rewrite Z.ltb_lt in * by lia | rewrite Z.ltb_ge in * by lia];
      pose proof (prefix_step_133 nums dens idx sum ltac:(lia) ltac:(lia) Hprefix);
      unfold problem_133_prefix_z in *; lia
  end.

Lemma proof_of_sum_squares_safety_wit_8 : sum_squares_safety_wit_8.
Proof.
  unfold sum_squares_safety_wit_8; left; intros; Intros; entailer!;
  get_pre_133 PreH8 i;
  pose proof (prefix_step_133 nums dens i sum ltac:(lia) ltac:(lia) PreH9);
  unfold problem_133_prefix_z in *;
  unfold ceil_ratio_133 in *; cbv zeta in *;
  destruct (0 <? Z.rem (Znth i nums 0) (Znth i dens 0)) eqn:E;
  try apply Z.ltb_lt in E; try apply Z.ltb_ge in E; lia.
Qed.

Lemma proof_of_sum_squares_safety_wit_9 : sum_squares_safety_wit_9.
Proof.
  unfold sum_squares_safety_wit_9; left; intros; Intros; entailer!;
  get_pre_133 PreH8 i;
  unfold ceil_ratio_133 in *; cbv zeta in *;
  destruct (0 <? Z.rem (Znth i nums 0) (Znth i dens 0)) eqn:E;
  try apply Z.ltb_lt in E; try apply Z.ltb_ge in E; lia.
Qed.

Lemma proof_of_sum_squares_safety_wit_10 : sum_squares_safety_wit_10.
Proof.
  unfold sum_squares_safety_wit_10; left; intros; Intros; entailer!;
  get_pre_133 PreH8 i;
  pose proof (prefix_step_133 nums dens i sum ltac:(lia) ltac:(lia) PreH9);
  unfold problem_133_prefix_z in *;
  unfold ceil_ratio_133 in *; cbv zeta in *;
  destruct (0 <? Z.rem (Znth i nums 0) (Znth i dens 0)) eqn:E;
  try apply Z.ltb_lt in E; try apply Z.ltb_ge in E; lia.
Qed.

Lemma proof_of_sum_squares_safety_wit_11 : sum_squares_safety_wit_11.
Proof.
  unfold sum_squares_safety_wit_11; left; intros; Intros; entailer!;
  get_pre_133 PreH8 i;
  unfold ceil_ratio_133 in *; cbv zeta in *;
  destruct (0 <? Z.rem (Znth i nums 0) (Znth i dens 0)) eqn:E;
  try apply Z.ltb_lt in E; try apply Z.ltb_ge in E; lia.
Qed.

Lemma proof_of_sum_squares_entail_wit_1 : sum_squares_entail_wit_1.
Proof.
  unfold sum_squares_entail_wit_1. right.
  intros. Intros. entailer!.
Qed.

Lemma proof_of_sum_squares_entail_wit_2_1 : sum_squares_entail_wit_2_1.
Proof.
  unfold sum_squares_entail_wit_2_1. right.
  intros. Intros. entailer!.
  pose proof (prefix_step_133 nums dens i sum ltac:(lia) ltac:(lia) PreH9).
  unfold ceil_ratio_133 in H; cbv zeta in H.
  destruct (0 <? Z.rem (Znth i nums 0) (Znth i dens 0)) eqn:E.
  - exact H.
  - apply Z.ltb_ge in E. exfalso. lia.
Qed.

Lemma proof_of_sum_squares_entail_wit_2_2 : sum_squares_entail_wit_2_2.
Proof.
  unfold sum_squares_entail_wit_2_2. right.
  intros. Intros. entailer!.
  pose proof (prefix_step_133 nums dens i sum ltac:(lia) ltac:(lia) PreH9).
  unfold ceil_ratio_133 in H; cbv zeta in H.
  destruct (0 <? Z.rem (Znth i nums 0) (Znth i dens 0)) eqn:E.
  - apply Z.ltb_lt in E. exfalso. lia.
  - exact H.
Qed.

Lemma proof_of_sum_squares_return_wit_1 : sum_squares_return_wit_1.
Proof.
  unfold sum_squares_return_wit_1. right.
  intros size_pre dens nums sum i Hiend Hi0 Hile Hmax
         Hnumslen Hdenslen Hpre Hprefix Hsize0 Hmax2
         Hnumslen2 Hdenslen2 Hpre2.
  assert (Hspec : problem_133_spec_z nums dens sum).
  { apply prefix_final_133 with (i := i).
    - lia.
    - lia.
    - exact Hprefix. }
  Intros. entailer!.
Qed.
