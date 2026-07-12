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
From SimpleC.EE.CAV.ground_truth_p160_do_algebra Require Import p160_do_algebra_goal.
From SimpleC.EE.CAV.ground_truth_p160_do_algebra Require Import p160_do_algebra_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import p160_do_algebra.
Local Open Scope sac.

(* BEGIN migrated companion-spec proofs *)
Module MigratedCompanionProofs.
Local Open Scope bool_scope.
Import ListNotations.
Open Scope Z_scope.
Import ListNotations.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope sac.



Lemma list_ascii_of_string_string_of_ascii_list_160 :
  forall l,
    list_ascii_of_string (string_of_ascii_list_160 l) = l.
Proof.
  induction l as [| c rest IH]; simpl; [reflexivity |].
  rewrite IH.
  reflexivity.
Qed.

Lemma Zlength_map_160 :
  forall {A B : Type} (f : A -> B) (l : list A),
    Zlength (map f l) = Zlength l.
Proof.
  intros A B f l.
  repeat rewrite Zlength_correct.
  rewrite map_length.
  reflexivity.
Qed.

Lemma Znth_map_160 :
  forall {A B : Type} (f : A -> B) l i da db,
    0 <= i < Zlength l ->
    Znth i (map f l) db = f (Znth i l da).
Proof.
  intros A B f l i da db Hi.
  unfold Znth.
  transitivity (nth (Z.to_nat i) (map f l) (f da)).
  - apply nth_indep.
    rewrite map_length.
    rewrite Zlength_correct in Hi.
    lia.
  - apply map_nth.
Qed.

Lemma operator_codes_prefix_snoc_160 :
  forall rows i,
    0 <= i < Zlength rows ->
    sublist 0 i (operator_codes_160 rows) ++
      operator_code_payload_160 (row_payload_z_160 (Znth i rows nil)) :: nil =
    sublist 0 (i + 1) (operator_codes_160 rows).
Proof.
  intros rows i Hi.
  rewrite (sublist_split 0 (i + 1) i (operator_codes_160 rows)) by
    (unfold operator_codes_160; try rewrite Zlength_map_160; lia).
  rewrite sublist_single with (d := 0) by
    (unfold operator_codes_160; try rewrite Zlength_map_160; lia).
  replace (Znth i (operator_codes_160 rows) 0) with
    (operator_code_payload_160 (row_payload_z_160 (Znth i rows nil))).
  2: {
    unfold operator_codes_160.
    rewrite (Znth_map_160 (fun row => operator_code_payload_160 (row_payload_z_160 row))
      rows i nil 0) by lia.
    reflexivity.
  }
  reflexivity.
Qed.

Lemma find_right_prefix_succ_160 :
  forall p ops lo i,
    lo <= i ->
    find_right_prefix_nat_160 (Z.to_nat (i + 1 - lo)) p ops lo =
    if p (Znth i ops 0)
    then i
    else find_right_prefix_nat_160 (Z.to_nat (i - lo)) p ops lo.
Proof.
  intros p ops lo i Hle.
  replace (i + 1 - lo) with (Z.succ (i - lo)) by lia.
  rewrite Z2Nat.inj_succ by lia.
  simpl.
  replace (lo + Z.of_nat (Z.to_nat (i - lo))) with i by lia.
  reflexivity.
Qed.

Lemma find_addsub_prefix_base_160 :
  forall ops lo,
    find_addsub_prefix_160 ops lo lo = -1.
Proof.
  intros. unfold find_addsub_prefix_160. replace (lo - lo) with 0 by lia. reflexivity.
Qed.

Lemma find_addsub_prefix_succ_hit_160 :
  forall ops lo i,
    lo <= i ->
    is_addsub_code_160 (Znth i ops 0) = true ->
    find_addsub_prefix_160 ops lo (i + 1) = i.
Proof.
  intros ops lo i Hle Hhit.
  unfold find_addsub_prefix_160.
  rewrite find_right_prefix_succ_160 by lia.
  rewrite Hhit. reflexivity.
Qed.

Lemma find_addsub_prefix_succ_miss_160 :
  forall ops lo i,
    lo <= i ->
    is_addsub_code_160 (Znth i ops 0) = false ->
    find_addsub_prefix_160 ops lo (i + 1) =
    find_addsub_prefix_160 ops lo i.
Proof.
  intros ops lo i Hle Hmiss.
  unfold find_addsub_prefix_160 at 1.
  rewrite find_right_prefix_succ_160 by lia.
  rewrite Hmiss. reflexivity.
Qed.

Lemma find_muldiv_prefix_base_160 :
  forall ops lo,
    find_muldiv_prefix_160 ops lo lo = -1.
Proof.
  intros. unfold find_muldiv_prefix_160. replace (lo - lo) with 0 by lia. reflexivity.
Qed.

Lemma find_muldiv_prefix_succ_hit_160 :
  forall ops lo i,
    lo <= i ->
    is_muldiv_code_160 (Znth i ops 0) = true ->
    find_muldiv_prefix_160 ops lo (i + 1) = i.
Proof.
  intros ops lo i Hle Hhit.
  unfold find_muldiv_prefix_160.
  rewrite find_right_prefix_succ_160 by lia.
  rewrite Hhit. reflexivity.
Qed.

Lemma find_muldiv_prefix_succ_miss_160 :
  forall ops lo i,
    lo <= i ->
    is_muldiv_code_160 (Znth i ops 0) = false ->
    find_muldiv_prefix_160 ops lo (i + 1) =
    find_muldiv_prefix_160 ops lo i.
Proof.
  intros ops lo i Hle Hmiss.
  unfold find_muldiv_prefix_160 at 1.
  rewrite find_right_prefix_succ_160 by lia.
  rewrite Hmiss. reflexivity.
Qed.

Lemma find_pow_left_prefix_succ_160 :
  forall ops lo i,
    lo <= i ->
    find_pow_left_prefix_160 ops lo (i + 1) =
    let prev := find_pow_left_prefix_160 ops lo i in
    if Z.eqb prev (-1)
    then if is_pow_code_160 (Znth i ops 0) then i else -1
    else prev.
Proof.
  intros ops lo i Hle.
  unfold find_pow_left_prefix_160.
  replace (i + 1 - lo) with (Z.succ (i - lo)) by lia.
  rewrite Z2Nat.inj_succ by lia.
  simpl.
  replace (lo + Z.of_nat (Z.to_nat (i - lo))) with i by lia.
  reflexivity.
Qed.

Lemma find_pow_left_prefix_base_160 :
  forall ops lo,
    find_pow_left_prefix_160 ops lo lo = -1.
Proof.
  intros. unfold find_pow_left_prefix_160. replace (lo - lo) with 0 by lia. reflexivity.
Qed.

Lemma find_pow_left_prefix_succ_first_160 :
  forall ops lo i,
    lo <= i ->
    find_pow_left_prefix_160 ops lo i = -1 ->
    is_pow_code_160 (Znth i ops 0) = true ->
    find_pow_left_prefix_160 ops lo (i + 1) = i.
Proof.
  intros ops lo i Hle Hprev Hhit.
  rewrite find_pow_left_prefix_succ_160 by lia.
  rewrite Hprev, Hhit. reflexivity.
Qed.

Lemma find_pow_left_prefix_succ_miss_160 :
  forall ops lo i,
    lo <= i ->
    find_pow_left_prefix_160 ops lo i = -1 ->
    is_pow_code_160 (Znth i ops 0) = false ->
    find_pow_left_prefix_160 ops lo (i + 1) = -1.
Proof.
  intros ops lo i Hle Hprev Hmiss.
  rewrite find_pow_left_prefix_succ_160 by lia.
  rewrite Hprev, Hmiss. reflexivity.
Qed.

Lemma find_pow_left_prefix_succ_keep_160 :
  forall ops lo i,
    lo <= i ->
    find_pow_left_prefix_160 ops lo i <> -1 ->
    find_pow_left_prefix_160 ops lo (i + 1) =
    find_pow_left_prefix_160 ops lo i.
Proof.
  intros ops lo i Hle Hprev.
  rewrite find_pow_left_prefix_succ_160 by lia.
  cbn zeta.
  destruct (Z.eqb (find_pow_left_prefix_160 ops lo i) (-1)) eqn:Heq.
  - apply Z.eqb_eq in Heq; contradiction.
  - reflexivity.
Qed.

Lemma find_right_prefix_nat_hit_160 :
  forall fuel p ops lo idx,
    idx = find_right_prefix_nat_160 fuel p ops lo ->
    0 <= idx ->
    p (Znth idx ops 0) = true.
Proof.
  induction fuel as [|fuel IH]; intros p ops lo idx Hidx Hnonneg; simpl in Hidx.
  - lia.
  - destruct (p (Znth (lo + Z.of_nat fuel) ops 0)) eqn:Hp.
    + subst idx. exact Hp.
    + eapply IH; eauto.
Qed.

Lemma find_right_prefix_nat_bound_160 :
  forall fuel p ops lo idx,
    idx = find_right_prefix_nat_160 fuel p ops lo ->
    0 <= idx ->
    lo <= idx < lo + Z.of_nat fuel.
Proof.
  induction fuel as [|fuel IH]; intros p ops lo idx Hidx Hnonneg; simpl in Hidx.
  - lia.
  - destruct (p (Znth (lo + Z.of_nat fuel) ops 0)) eqn:Hp.
    + subst idx. lia.
    + pose proof (IH p ops lo idx Hidx Hnonneg) as Hbound. lia.
Qed.

Lemma find_addsub_prefix_bound_160 :
  forall ops lo hi idx,
    idx = find_addsub_prefix_160 ops lo hi ->
    0 <= idx ->
    lo <= idx < hi.
Proof.
  intros ops lo hi idx Hfind Hidx.
  unfold find_addsub_prefix_160 in Hfind.
  pose proof (find_right_prefix_nat_bound_160 _ _ _ _ _ Hfind Hidx) as Hbound.
  assert (0 <= hi - lo).
  { destruct (Z_le_gt_dec 0 (hi - lo)); [lia|].
    assert (Z.to_nat (hi - lo) = 0%nat) by lia.
    rewrite H in Hbound; lia. }
  rewrite Z2Nat.id in Hbound by lia.
  lia.
Qed.

Lemma find_muldiv_prefix_bound_160 :
  forall ops lo hi idx,
    idx = find_muldiv_prefix_160 ops lo hi ->
    0 <= idx ->
    lo <= idx < hi.
Proof.
  intros ops lo hi idx Hfind Hidx.
  unfold find_muldiv_prefix_160 in Hfind.
  pose proof (find_right_prefix_nat_bound_160 _ _ _ _ _ Hfind Hidx) as Hbound.
  assert (0 <= hi - lo).
  { destruct (Z_le_gt_dec 0 (hi - lo)); [lia|].
    assert (Z.to_nat (hi - lo) = 0%nat) by lia.
    rewrite H in Hbound; lia. }
  rewrite Z2Nat.id in Hbound by lia.
  lia.
Qed.

Lemma find_pow_left_prefix_nat_bound_160 :
  forall fuel ops lo idx,
    idx = find_pow_left_prefix_nat_160 fuel ops lo ->
    0 <= idx ->
    lo <= idx < lo + Z.of_nat fuel.
Proof.
  induction fuel as [|fuel IH]; intros ops lo idx Hidx Hnonneg; simpl in Hidx.
  - lia.
  - destruct (Z.eqb (find_pow_left_prefix_nat_160 fuel ops lo) (-1)) eqn:Hprev.
    + destruct (is_pow_code_160 (Znth (lo + Z.of_nat fuel) ops 0)) eqn:Hpow.
      * subst idx. lia.
      * lia.
    + pose proof (IH ops lo idx Hidx Hnonneg) as Hbound. lia.
Qed.

Lemma find_pow_left_prefix_bound_160 :
  forall ops lo hi idx,
    idx = find_pow_left_prefix_160 ops lo hi ->
    0 <= idx ->
    lo <= idx < hi.
Proof.
  intros ops lo hi idx Hfind Hidx.
  unfold find_pow_left_prefix_160 in Hfind.
  pose proof (find_pow_left_prefix_nat_bound_160 _ _ _ _ Hfind Hidx) as Hbound.
  assert (0 <= hi - lo).
  { destruct (Z_le_gt_dec 0 (hi - lo)); [lia|].
    assert (Z.to_nat (hi - lo) = 0%nat) by lia.
    rewrite H in Hbound; lia. }
  rewrite Z2Nat.id in Hbound by lia.
  lia.
Qed.

Lemma find_pow_left_prefix_nat_hit_160 :
  forall fuel ops lo idx,
    idx = find_pow_left_prefix_nat_160 fuel ops lo ->
    0 <= idx ->
    is_pow_code_160 (Znth idx ops 0) = true.
Proof.
  induction fuel as [|fuel IH]; intros ops lo idx Hidx Hnonneg; simpl in Hidx.
  - lia.
  - destruct (Z.eqb (find_pow_left_prefix_nat_160 fuel ops lo) (-1)) eqn:Hprev.
    + destruct (is_pow_code_160 (Znth (lo + Z.of_nat fuel) ops 0)) eqn:Hpow.
      * subst idx. exact Hpow.
      * lia.
    + eapply IH; eauto.
Qed.

Lemma find_pow_left_prefix_hit_is_four_160 :
  forall ops lo hi idx,
    idx = find_pow_left_prefix_160 ops lo hi ->
    0 <= idx ->
    Znth idx ops 0 = 4.
Proof.
  intros ops lo hi idx Hfind Hidx.
  unfold find_pow_left_prefix_160 in Hfind.
  pose proof (find_pow_left_prefix_nat_hit_160 _ _ _ _ Hfind Hidx) as Hhit.
  unfold is_pow_code_160 in Hhit.
  apply Z.eqb_eq in Hhit.
  exact Hhit.
Qed.

Lemma find_addsub_prefix_nonzero_is_one_160 :
  forall ops lo hi idx,
    idx = find_addsub_prefix_160 ops lo hi ->
    0 <= idx ->
    Znth idx ops 0 <> 0 ->
    Znth idx ops 0 = 1.
Proof.
  intros ops lo hi idx Hfind Hidx Hnz.
  unfold find_addsub_prefix_160 in Hfind.
  pose proof (find_right_prefix_nat_hit_160 _ _ _ _ _ Hfind Hidx) as Hhit.
  unfold is_addsub_code_160 in Hhit.
  apply orb_true_iff in Hhit as [H0 | H1].
  - apply Z.eqb_eq in H0; lia.
  - apply Z.eqb_eq in H1; exact H1.
Qed.

Lemma find_muldiv_prefix_not_two_is_three_160 :
  forall ops lo hi idx,
    idx = find_muldiv_prefix_160 ops lo hi ->
    0 <= idx ->
    Znth idx ops 0 <> 2 ->
    Znth idx ops 0 = 3.
Proof.
  intros ops lo hi idx Hfind Hidx Hnz.
  unfold find_muldiv_prefix_160 in Hfind.
  pose proof (find_right_prefix_nat_hit_160 _ _ _ _ _ Hfind Hidx) as Hhit.
  unfold is_muldiv_code_160 in Hhit.
  apply orb_true_iff in Hhit as [H2 | H3].
  - apply Z.eqb_eq in H2; lia.
  - apply Z.eqb_eq in H3; exact H3.
Qed.

Lemma eval_range_base_160 :
  forall ops nums lo,
    eval_range_160 ops nums lo lo = Znth lo nums 0.
Proof.
  intros ops nums lo.
  unfold eval_range_160.
  replace (lo - lo + 1) with 1 by lia.
  change (Z.to_nat 1) with 1%nat.
  simpl. rewrite Z.eqb_refl.
  reflexivity.
Qed.

Lemma eval_range_no_operator_160 :
  forall ops nums lo hi,
    lo < hi ->
    find_addsub_prefix_160 ops lo hi < 0 ->
    find_muldiv_prefix_160 ops lo hi < 0 ->
    find_pow_left_prefix_160 ops lo hi < 0 ->
    eval_range_160 ops nums lo hi = 0.
Proof.
  intros ops nums lo hi Hlt Hadd Hmul Hpow.
  unfold eval_range_160.
  assert (0 < hi - lo + 1) by lia.
  destruct (Z.to_nat (hi - lo + 1)) eqn:Hfuel; [lia |].
  simpl.
  replace (Z.eqb lo hi) with false by (symmetry; apply Z.eqb_neq; lia).
  destruct (Z.geb (find_addsub_prefix_160 ops lo hi) 0) eqn:Hadd_ge.
  { apply Z.geb_le in Hadd_ge; lia. }
  destruct (Z.geb (find_muldiv_prefix_160 ops lo hi) 0) eqn:Hmul_ge.
  { apply Z.geb_le in Hmul_ge; lia. }
  destruct (Z.geb (find_pow_left_prefix_160 ops lo hi) 0) eqn:Hpow_ge.
  { apply Z.geb_le in Hpow_ge; lia. }
  reflexivity.
Qed.

Lemma sub_fuel_left_160 :
  forall lo hi idx need,
    lo <= idx < hi ->
    Z.to_nat (hi - lo + 1) = S need ->
    (Z.to_nat (idx - lo + 1) <= need)%nat.
Proof.
  intros lo hi idx need Hbound Hneed.
  replace (hi - lo + 1) with (Z.succ (hi - lo)) in Hneed by lia.
  rewrite Z2Nat.inj_succ in Hneed by lia.
  inversion Hneed; subst need.
  apply Z2Nat.inj_le; lia.
Qed.

Lemma sub_fuel_right_160 :
  forall lo hi idx need,
    lo <= idx < hi ->
    Z.to_nat (hi - lo + 1) = S need ->
    (Z.to_nat (hi - (idx + 1) + 1) <= need)%nat.
Proof.
  intros lo hi idx need Hbound Hneed.
  replace (hi - lo + 1) with (Z.succ (hi - lo)) in Hneed by lia.
  rewrite Z2Nat.inj_succ in Hneed by lia.
  inversion Hneed; subst need.
  apply Z2Nat.inj_le; lia.
Qed.

Lemma sub_fuel_left_lt_160 :
  forall lo hi idx,
    lo <= idx < hi ->
    (Z.to_nat (idx - lo + 1) < Z.to_nat (hi - lo + 1))%nat.
Proof.
  intros lo hi idx Hbound.
  apply Z2Nat.inj_lt; lia.
Qed.

Lemma sub_fuel_right_lt_160 :
  forall lo hi idx,
    lo <= idx < hi ->
    (Z.to_nat (hi - (idx + 1) + 1) < Z.to_nat (hi - lo + 1))%nat.
Proof.
  intros lo hi idx Hbound.
  apply Z2Nat.inj_lt; lia.
Qed.

Lemma eval_range_safe_fuel_shrink_160 :
  forall source target ops nums lo hi,
    eval_range_safe_fuel_160 source ops nums lo hi ->
    (Z.to_nat (hi - lo + 1) <= target)%nat ->
    (target <= source)%nat ->
    eval_range_safe_fuel_160 target ops nums lo hi.
Proof.
  induction source as [source IH] using lt_wf_ind.
  intros target ops nums lo hi Hsafe Htarget Hle.
  destruct source as [|source']; [contradiction|].
  simpl in Hsafe.
  destruct Hsafe as [Hlohi [Hnum [Hops Hsafe]]].
  assert (Hexact_pos : Z.to_nat (hi - lo + 1) <> O).
  {
    intro Hz.
    apply (f_equal Z.of_nat) in Hz.
    rewrite Nat2Z.inj_0 in Hz.
    rewrite Z2Nat.id in Hz by lia.
    lia.
  }
  destruct target as [|target']; [lia|].
  simpl.
  split; [exact Hlohi|].
  split; [exact Hnum|].
  split; [exact Hops|].
  destruct (Z.eqb lo hi) eqn:Hbase; [exact Hsafe|].
  assert (Hlt : lo < hi) by (apply Z.eqb_neq in Hbase; lia).
  destruct (Z.geb (find_addsub_prefix_160 ops lo hi) 0) eqn:Hadd_ge.
  - destruct Hsafe as [Hleft [Hright Hrange]].
    pose proof Hadd_ge as Hadd_nonneg.
    apply Z.geb_le in Hadd_nonneg.
    pose proof (find_addsub_prefix_bound_160 ops lo hi
      (find_addsub_prefix_160 ops lo hi) eq_refl Hadd_nonneg) as Hbound.
    split.
    + eapply (IH source'); [lia | exact Hleft | | lia].
      pose proof (sub_fuel_left_lt_160 lo hi
        (find_addsub_prefix_160 ops lo hi) Hbound) as Hsub.
      lia.
    + split.
      * eapply (IH source'); [lia | exact Hright | | lia].
      pose proof (sub_fuel_right_lt_160 lo hi
        (find_addsub_prefix_160 ops lo hi) Hbound) as Hsub.
      lia.
      * exact Hrange.
  - destruct (Z.geb (find_muldiv_prefix_160 ops lo hi) 0) eqn:Hmul_ge.
    + destruct Hsafe as [Hleft [Hright [Hdiv [Hover Hrange]]]].
      pose proof Hmul_ge as Hmul_nonneg.
      apply Z.geb_le in Hmul_nonneg.
      pose proof (find_muldiv_prefix_bound_160 ops lo hi
        (find_muldiv_prefix_160 ops lo hi) eq_refl Hmul_nonneg) as Hbound.
      split.
      * eapply (IH source'); [lia | exact Hleft | | lia].
        pose proof (sub_fuel_left_lt_160 lo hi
          (find_muldiv_prefix_160 ops lo hi) Hbound) as Hsub.
        lia.
      * split.
        -- eapply (IH source'); [lia | exact Hright | | lia].
        pose proof (sub_fuel_right_lt_160 lo hi
          (find_muldiv_prefix_160 ops lo hi) Hbound) as Hsub.
        lia.
        -- split; [exact Hdiv|].
           split; [exact Hover|exact Hrange].
    + destruct (Z.geb (find_pow_left_prefix_160 ops lo hi) 0) eqn:Hpow_ge.
      * destruct Hsafe as [Hleft [Hright [Hexp_nonneg [Hexp_bound [Hpow Hrange]]]]].
        pose proof Hpow_ge as Hpow_nonneg.
        apply Z.geb_le in Hpow_nonneg.
        pose proof (find_pow_left_prefix_bound_160 ops lo hi
          (find_pow_left_prefix_160 ops lo hi) eq_refl Hpow_nonneg) as Hbound.
        split.
        -- eapply (IH source'); [lia | exact Hleft | | lia].
           pose proof (sub_fuel_left_lt_160 lo hi
             (find_pow_left_prefix_160 ops lo hi) Hbound) as Hsub.
           lia.
        -- split.
           ++ eapply (IH source'); [lia | exact Hright | | lia].
           pose proof (sub_fuel_right_lt_160 lo hi
             (find_pow_left_prefix_160 ops lo hi) Hbound) as Hsub.
           lia.
           ++ split; [exact Hexp_nonneg|].
              split; [exact Hexp_bound|].
              split; [exact Hpow|exact Hrange].
      * exact Hsafe.
Qed.

Lemma eval_range_safe_addsub_left_160 :
  forall ops nums lo hi idx,
    lo < hi ->
    0 <= idx ->
    idx = find_addsub_prefix_160 ops lo hi ->
    eval_range_safe_160 ops nums lo hi ->
    eval_range_safe_160 ops nums lo idx.
Proof.
  intros ops nums lo hi idx Hlt Hidx Hfind Hsafe.
  unfold eval_range_safe_160 in *.
  assert (0 < hi - lo + 1) by lia.
  destruct (Z.to_nat (hi - lo + 1)) eqn:Hfuel; [lia|].
  simpl in Hsafe.
  destruct Hsafe as [_ [_ [_ Hsafe]]].
  replace (Z.eqb lo hi) with false in Hsafe by (symmetry; apply Z.eqb_neq; lia).
  rewrite <- Hfind in Hsafe.
  replace (Z.geb idx 0) with true in Hsafe by (symmetry; apply Z.geb_le; lia).
  destruct Hsafe as [Hleft _].
  pose proof (find_addsub_prefix_bound_160 ops lo hi idx Hfind Hidx) as Hbound.
  eapply eval_range_safe_fuel_shrink_160; [exact Hleft| |].
  - lia.
  - eapply sub_fuel_left_160; [exact Hbound|exact Hfuel].
Qed.

Lemma eval_range_safe_addsub_right_160 :
  forall ops nums lo hi idx,
    lo < hi ->
    0 <= idx ->
    idx = find_addsub_prefix_160 ops lo hi ->
    eval_range_safe_160 ops nums lo hi ->
    eval_range_safe_160 ops nums (idx + 1) hi.
Proof.
  intros ops nums lo hi idx Hlt Hidx Hfind Hsafe.
  unfold eval_range_safe_160 in *.
  assert (0 < hi - lo + 1) by lia.
  destruct (Z.to_nat (hi - lo + 1)) eqn:Hfuel; [lia|].
  simpl in Hsafe.
  destruct Hsafe as [_ [_ [_ Hsafe]]].
  replace (Z.eqb lo hi) with false in Hsafe by (symmetry; apply Z.eqb_neq; lia).
  rewrite <- Hfind in Hsafe.
  replace (Z.geb idx 0) with true in Hsafe by (symmetry; apply Z.geb_le; lia).
  destruct Hsafe as [_ [Hright _]].
  pose proof (find_addsub_prefix_bound_160 ops lo hi idx Hfind Hidx) as Hbound.
  eapply eval_range_safe_fuel_shrink_160; [exact Hright| |].
  - lia.
  - eapply sub_fuel_right_160; [exact Hbound|exact Hfuel].
Qed.

Lemma eval_range_safe_muldiv_left_160 :
  forall ops nums lo hi idx,
    lo < hi ->
    0 <= idx ->
    find_addsub_prefix_160 ops lo hi < 0 ->
    idx = find_muldiv_prefix_160 ops lo hi ->
    eval_range_safe_160 ops nums lo hi ->
    eval_range_safe_160 ops nums lo idx.
Proof.
  intros ops nums lo hi idx Hlt Hidx Hadd Hfind Hsafe.
  unfold eval_range_safe_160 in *.
  assert (0 < hi - lo + 1) by lia.
  destruct (Z.to_nat (hi - lo + 1)) eqn:Hfuel; [lia|].
  simpl in Hsafe.
  destruct Hsafe as [_ [_ [_ Hsafe]]].
  replace (Z.eqb lo hi) with false in Hsafe by (symmetry; apply Z.eqb_neq; lia).
  destruct (Z.geb (find_addsub_prefix_160 ops lo hi) 0) eqn:Hadd_ge.
  { apply Z.geb_le in Hadd_ge; lia. }
  rewrite <- Hfind in Hsafe.
  replace (Z.geb idx 0) with true in Hsafe by (symmetry; apply Z.geb_le; lia).
  destruct Hsafe as [Hleft _].
  pose proof (find_muldiv_prefix_bound_160 ops lo hi idx Hfind Hidx) as Hbound.
  eapply eval_range_safe_fuel_shrink_160; [exact Hleft| |].
  - lia.
  - eapply sub_fuel_left_160; [exact Hbound|exact Hfuel].
Qed.

Lemma eval_range_safe_muldiv_right_160 :
  forall ops nums lo hi idx,
    lo < hi ->
    0 <= idx ->
    find_addsub_prefix_160 ops lo hi < 0 ->
    idx = find_muldiv_prefix_160 ops lo hi ->
    eval_range_safe_160 ops nums lo hi ->
    eval_range_safe_160 ops nums (idx + 1) hi.
Proof.
  intros ops nums lo hi idx Hlt Hidx Hadd Hfind Hsafe.
  unfold eval_range_safe_160 in *.
  assert (0 < hi - lo + 1) by lia.
  destruct (Z.to_nat (hi - lo + 1)) eqn:Hfuel; [lia|].
  simpl in Hsafe.
  destruct Hsafe as [_ [_ [_ Hsafe]]].
  replace (Z.eqb lo hi) with false in Hsafe by (symmetry; apply Z.eqb_neq; lia).
  destruct (Z.geb (find_addsub_prefix_160 ops lo hi) 0) eqn:Hadd_ge.
  { apply Z.geb_le in Hadd_ge; lia. }
  rewrite <- Hfind in Hsafe.
  replace (Z.geb idx 0) with true in Hsafe by (symmetry; apply Z.geb_le; lia).
  destruct Hsafe as [_ [Hright _]].
  pose proof (find_muldiv_prefix_bound_160 ops lo hi idx Hfind Hidx) as Hbound.
  eapply eval_range_safe_fuel_shrink_160; [exact Hright| |].
  - lia.
  - eapply sub_fuel_right_160; [exact Hbound|exact Hfuel].
Qed.

Lemma eval_range_safe_pow_left_160 :
  forall ops nums lo hi idx,
    lo < hi ->
    0 <= idx ->
    find_addsub_prefix_160 ops lo hi < 0 ->
    find_muldiv_prefix_160 ops lo hi < 0 ->
    idx = find_pow_left_prefix_160 ops lo hi ->
    eval_range_safe_160 ops nums lo hi ->
    eval_range_safe_160 ops nums lo idx.
Proof.
  intros ops nums lo hi idx Hlt Hidx Hadd Hmul Hfind Hsafe.
  unfold eval_range_safe_160 in *.
  assert (0 < hi - lo + 1) by lia.
  destruct (Z.to_nat (hi - lo + 1)) eqn:Hfuel; [lia|].
  simpl in Hsafe.
  destruct Hsafe as [_ [_ [_ Hsafe]]].
  replace (Z.eqb lo hi) with false in Hsafe by (symmetry; apply Z.eqb_neq; lia).
  destruct (Z.geb (find_addsub_prefix_160 ops lo hi) 0) eqn:Hadd_ge.
  { apply Z.geb_le in Hadd_ge; lia. }
  destruct (Z.geb (find_muldiv_prefix_160 ops lo hi) 0) eqn:Hmul_ge.
  { apply Z.geb_le in Hmul_ge; lia. }
  rewrite <- Hfind in Hsafe.
  replace (Z.geb idx 0) with true in Hsafe by (symmetry; apply Z.geb_le; lia).
  destruct Hsafe as [Hleft _].
  pose proof (find_pow_left_prefix_bound_160 ops lo hi idx Hfind Hidx) as Hbound.
  eapply eval_range_safe_fuel_shrink_160; [exact Hleft| |].
  - lia.
  - eapply sub_fuel_left_160; [exact Hbound|exact Hfuel].
Qed.

Lemma eval_range_safe_pow_right_160 :
  forall ops nums lo hi idx,
    lo < hi ->
    0 <= idx ->
    find_addsub_prefix_160 ops lo hi < 0 ->
    find_muldiv_prefix_160 ops lo hi < 0 ->
    idx = find_pow_left_prefix_160 ops lo hi ->
    eval_range_safe_160 ops nums lo hi ->
    eval_range_safe_160 ops nums (idx + 1) hi.
Proof.
  intros ops nums lo hi idx Hlt Hidx Hadd Hmul Hfind Hsafe.
  unfold eval_range_safe_160 in *.
  assert (0 < hi - lo + 1) by lia.
  destruct (Z.to_nat (hi - lo + 1)) eqn:Hfuel; [lia|].
  simpl in Hsafe.
  destruct Hsafe as [_ [_ [_ Hsafe]]].
  replace (Z.eqb lo hi) with false in Hsafe by (symmetry; apply Z.eqb_neq; lia).
  destruct (Z.geb (find_addsub_prefix_160 ops lo hi) 0) eqn:Hadd_ge.
  { apply Z.geb_le in Hadd_ge; lia. }
  destruct (Z.geb (find_muldiv_prefix_160 ops lo hi) 0) eqn:Hmul_ge.
  { apply Z.geb_le in Hmul_ge; lia. }
  rewrite <- Hfind in Hsafe.
  replace (Z.geb idx 0) with true in Hsafe by (symmetry; apply Z.geb_le; lia).
  destruct Hsafe as [_ [Hright _]].
  pose proof (find_pow_left_prefix_bound_160 ops lo hi idx Hfind Hidx) as Hbound.
  eapply eval_range_safe_fuel_shrink_160; [exact Hright| |].
  - lia.
  - eapply sub_fuel_right_160; [exact Hbound|exact Hfuel].
Qed.

Lemma eval_range_fuel_safe_enough_gen_160 :
  forall fuel safe_fuel ops nums lo hi,
    eval_range_safe_fuel_160 safe_fuel ops nums lo hi ->
    (Z.to_nat (hi - lo + 1) <= fuel)%nat ->
    (Z.to_nat (hi - lo + 1) <= safe_fuel)%nat ->
    eval_range_fuel_160 fuel ops nums lo hi =
    eval_range_160 ops nums lo hi.
Proof.
  induction fuel as [fuel IH] using lt_wf_ind.
  intros safe_fuel ops nums lo hi Hsafe Hfuel Hsafe_fuel.
  unfold eval_range_160.
  remember (Z.to_nat (hi - lo + 1)) as exact eqn:Hexact.
  destruct safe_fuel as [|safe_fuel'].
  { contradiction. }
  simpl in Hsafe.
  destruct Hsafe as [Hlohi [Hnum [Hops Hsafe]]].
  assert (Hexact_pos : exact <> O).
  {
    subst exact.
    intro Hz.
    apply (f_equal Z.of_nat) in Hz.
    rewrite Nat2Z.inj_0 in Hz.
    rewrite Z2Nat.id in Hz by lia.
    lia.
  }
  destruct fuel as [|fuel'].
  { lia. }
  destruct exact as [|exact']; [contradiction|].
  simpl.
  destruct (Z.eqb lo hi) eqn:Hbase; [reflexivity|].
  assert (Hlt : lo < hi) by (apply Z.eqb_neq in Hbase; lia).
  destruct (Z.geb (find_addsub_prefix_160 ops lo hi) 0) eqn:Hadd_ge.
  - destruct Hsafe as [Hleft [Hright _]].
    pose proof Hadd_ge as Hadd_nonneg.
    apply Z.geb_le in Hadd_nonneg.
    pose proof (find_addsub_prefix_bound_160 ops lo hi
      (find_addsub_prefix_160 ops lo hi) eq_refl Hadd_nonneg) as Hbound.
    rewrite (IH fuel' ltac:(lia) safe_fuel' ops nums lo
      (find_addsub_prefix_160 ops lo hi) Hleft).
    2: {
      eapply Nat.le_trans.
      - eapply sub_fuel_left_160; eauto.
      - lia.
    }
    2: {
      eapply Nat.le_trans.
      - eapply sub_fuel_left_160; eauto.
      - lia.
    }
    rewrite (IH fuel' ltac:(lia) safe_fuel' ops nums
      (find_addsub_prefix_160 ops lo hi + 1) hi Hright).
    2: {
      eapply Nat.le_trans.
      - eapply sub_fuel_right_160; eauto.
      - lia.
    }
    2: {
      eapply Nat.le_trans.
      - eapply sub_fuel_right_160; eauto.
      - lia.
    }
    rewrite (IH exact' ltac:(lia) safe_fuel' ops nums lo
      (find_addsub_prefix_160 ops lo hi) Hleft).
    2: { eapply sub_fuel_left_160; eauto. }
    2: {
      eapply Nat.le_trans.
      - eapply sub_fuel_left_160; eauto.
      - lia.
    }
    rewrite (IH exact' ltac:(lia) safe_fuel' ops nums
      (find_addsub_prefix_160 ops lo hi + 1) hi Hright).
    2: { eapply sub_fuel_right_160; eauto. }
    2: {
      eapply Nat.le_trans.
      - eapply sub_fuel_right_160; eauto.
      - lia.
    }
    reflexivity.
  - destruct (Z.geb (find_muldiv_prefix_160 ops lo hi) 0) eqn:Hmul_ge.
    + destruct Hsafe as [Hleft [Hright _]].
      pose proof Hmul_ge as Hmul_nonneg.
      apply Z.geb_le in Hmul_nonneg.
      pose proof (find_muldiv_prefix_bound_160 ops lo hi
        (find_muldiv_prefix_160 ops lo hi) eq_refl Hmul_nonneg) as Hbound.
      rewrite (IH fuel' ltac:(lia) safe_fuel' ops nums lo
        (find_muldiv_prefix_160 ops lo hi) Hleft).
      2: {
        eapply Nat.le_trans.
        - eapply sub_fuel_left_160; eauto.
        - lia.
      }
      2: {
        eapply Nat.le_trans.
        - eapply sub_fuel_left_160; eauto.
        - lia.
      }
      rewrite (IH fuel' ltac:(lia) safe_fuel' ops nums
        (find_muldiv_prefix_160 ops lo hi + 1) hi Hright).
      2: {
        eapply Nat.le_trans.
        - eapply sub_fuel_right_160; eauto.
        - lia.
      }
      2: {
        eapply Nat.le_trans.
        - eapply sub_fuel_right_160; eauto.
        - lia.
      }
      rewrite (IH exact' ltac:(lia) safe_fuel' ops nums lo
        (find_muldiv_prefix_160 ops lo hi) Hleft).
      2: { eapply sub_fuel_left_160; eauto. }
      2: {
        eapply Nat.le_trans.
        - eapply sub_fuel_left_160; eauto.
        - lia.
      }
      rewrite (IH exact' ltac:(lia) safe_fuel' ops nums
        (find_muldiv_prefix_160 ops lo hi + 1) hi Hright).
      2: { eapply sub_fuel_right_160; eauto. }
      2: {
        eapply Nat.le_trans.
        - eapply sub_fuel_right_160; eauto.
        - lia.
      }
      reflexivity.
    + destruct (Z.geb (find_pow_left_prefix_160 ops lo hi) 0) eqn:Hpow_ge.
      * destruct Hsafe as [Hleft [Hright _]].
        pose proof Hpow_ge as Hpow_nonneg.
        apply Z.geb_le in Hpow_nonneg.
        pose proof (find_pow_left_prefix_bound_160 ops lo hi
          (find_pow_left_prefix_160 ops lo hi) eq_refl Hpow_nonneg) as Hbound.
        rewrite (IH fuel' ltac:(lia) safe_fuel' ops nums lo
          (find_pow_left_prefix_160 ops lo hi) Hleft).
        2: {
          eapply Nat.le_trans.
          - eapply sub_fuel_left_160; eauto.
          - lia.
        }
        2: {
          eapply Nat.le_trans.
          - eapply sub_fuel_left_160; eauto.
          - lia.
        }
        rewrite (IH fuel' ltac:(lia) safe_fuel' ops nums
          (find_pow_left_prefix_160 ops lo hi + 1) hi Hright).
        2: {
          eapply Nat.le_trans.
          - eapply sub_fuel_right_160; eauto.
          - lia.
        }
        2: {
          eapply Nat.le_trans.
          - eapply sub_fuel_right_160; eauto.
          - lia.
        }
        rewrite (IH exact' ltac:(lia) safe_fuel' ops nums lo
          (find_pow_left_prefix_160 ops lo hi) Hleft).
        2: { eapply sub_fuel_left_160; eauto. }
        2: {
          eapply Nat.le_trans.
          - eapply sub_fuel_left_160; eauto.
          - lia.
        }
        rewrite (IH exact' ltac:(lia) safe_fuel' ops nums
          (find_pow_left_prefix_160 ops lo hi + 1) hi Hright).
        2: { eapply sub_fuel_right_160; eauto. }
        2: {
          eapply Nat.le_trans.
          - eapply sub_fuel_right_160; eauto.
          - lia.
        }
        reflexivity.
      * reflexivity.
Qed.

Lemma eval_range_addsub_unfold_160 :
  forall ops nums lo hi idx,
    lo < hi ->
    0 <= idx ->
    idx = find_addsub_prefix_160 ops lo hi ->
    eval_range_safe_160 ops nums lo hi ->
    eval_range_160 ops nums lo hi =
    apply_code_160 (Znth idx ops 0)
      (eval_range_160 ops nums lo idx)
      (eval_range_160 ops nums (idx + 1) hi).
Proof.
  intros ops nums lo hi idx Hlt Hidx Hfind Hsafe.
  unfold eval_range_160 at 1.
  assert (0 < hi - lo + 1) by lia.
  destruct (Z.to_nat (hi - lo + 1)) eqn:Hfuel; [lia |].
  simpl.
  replace (Z.eqb lo hi) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite <- Hfind.
  replace (Z.geb idx 0) with true by (symmetry; apply Z.geb_le; lia).
  unfold eval_range_safe_160 in Hsafe.
  rewrite Hfuel in Hsafe.
  simpl in Hsafe.
  destruct Hsafe as [_ [_ [_ Hsafe]]].
  replace (Z.eqb lo hi) with false in Hsafe by (symmetry; apply Z.eqb_neq; lia).
  rewrite <- Hfind in Hsafe.
  replace (Z.geb idx 0) with true in Hsafe by (symmetry; apply Z.geb_le; lia).
  destruct Hsafe as [Hleft [Hright _]].
  pose proof (find_addsub_prefix_bound_160 ops lo hi idx Hfind Hidx) as Hbound.
  rewrite (eval_range_fuel_safe_enough_gen_160 n n ops nums lo idx Hleft).
  2: { eapply sub_fuel_left_160; eauto. }
  2: { eapply sub_fuel_left_160; eauto. }
  rewrite (eval_range_fuel_safe_enough_gen_160 n n ops nums (idx + 1) hi Hright).
  2: { eapply sub_fuel_right_160; eauto. }
  2: { eapply sub_fuel_right_160; eauto. }
  reflexivity.
Qed.

Lemma eval_range_muldiv_unfold_160 :
  forall ops nums lo hi idx,
    lo < hi ->
    0 <= idx ->
    find_addsub_prefix_160 ops lo hi < 0 ->
    idx = find_muldiv_prefix_160 ops lo hi ->
    eval_range_safe_160 ops nums lo hi ->
    eval_range_160 ops nums lo hi =
    apply_code_160 (Znth idx ops 0)
      (eval_range_160 ops nums lo idx)
      (eval_range_160 ops nums (idx + 1) hi).
Proof.
  intros ops nums lo hi idx Hlt Hidx Hadd Hfind Hsafe.
  unfold eval_range_160 at 1.
  assert (0 < hi - lo + 1) by lia.
  destruct (Z.to_nat (hi - lo + 1)) eqn:Hfuel; [lia |].
  simpl.
  replace (Z.eqb lo hi) with false by (symmetry; apply Z.eqb_neq; lia).
  destruct (Z.geb (find_addsub_prefix_160 ops lo hi) 0) eqn:Hadd_ge.
  { apply Z.geb_le in Hadd_ge; lia. }
  rewrite <- Hfind.
  replace (Z.geb idx 0) with true by (symmetry; apply Z.geb_le; lia).
  unfold eval_range_safe_160 in Hsafe.
  rewrite Hfuel in Hsafe.
  simpl in Hsafe.
  destruct Hsafe as [_ [_ [_ Hsafe]]].
  replace (Z.eqb lo hi) with false in Hsafe by (symmetry; apply Z.eqb_neq; lia).
  destruct (Z.geb (find_addsub_prefix_160 ops lo hi) 0) eqn:Hadd_ge2.
  { apply Z.geb_le in Hadd_ge2; lia. }
  rewrite <- Hfind in Hsafe.
  replace (Z.geb idx 0) with true in Hsafe by (symmetry; apply Z.geb_le; lia).
  destruct Hsafe as [Hleft [Hright _]].
  pose proof (find_muldiv_prefix_bound_160 ops lo hi idx Hfind Hidx) as Hbound.
  rewrite (eval_range_fuel_safe_enough_gen_160 n n ops nums lo idx Hleft).
  2: { eapply sub_fuel_left_160; eauto. }
  2: { eapply sub_fuel_left_160; eauto. }
  rewrite (eval_range_fuel_safe_enough_gen_160 n n ops nums (idx + 1) hi Hright).
  2: { eapply sub_fuel_right_160; eauto. }
  2: { eapply sub_fuel_right_160; eauto. }
  reflexivity.
Qed.

Lemma eval_range_pow_unfold_160 :
  forall ops nums lo hi idx,
    lo < hi ->
    0 <= idx ->
    find_addsub_prefix_160 ops lo hi < 0 ->
    find_muldiv_prefix_160 ops lo hi < 0 ->
    idx = find_pow_left_prefix_160 ops lo hi ->
    eval_range_safe_160 ops nums lo hi ->
    eval_range_160 ops nums lo hi =
    apply_code_160 (Znth idx ops 0)
      (eval_range_160 ops nums lo idx)
      (eval_range_160 ops nums (idx + 1) hi).
Proof.
  intros ops nums lo hi idx Hlt Hidx Hadd Hmul Hfind Hsafe.
  unfold eval_range_160 at 1.
  assert (0 < hi - lo + 1) by lia.
  destruct (Z.to_nat (hi - lo + 1)) eqn:Hfuel; [lia |].
  simpl.
  replace (Z.eqb lo hi) with false by (symmetry; apply Z.eqb_neq; lia).
  destruct (Z.geb (find_addsub_prefix_160 ops lo hi) 0) eqn:Hadd_ge.
  { apply Z.geb_le in Hadd_ge; lia. }
  destruct (Z.geb (find_muldiv_prefix_160 ops lo hi) 0) eqn:Hmul_ge.
  { apply Z.geb_le in Hmul_ge; lia. }
  rewrite <- Hfind.
  replace (Z.geb idx 0) with true by (symmetry; apply Z.geb_le; lia).
  unfold eval_range_safe_160 in Hsafe.
  rewrite Hfuel in Hsafe.
  simpl in Hsafe.
  destruct Hsafe as [_ [_ [_ Hsafe]]].
  replace (Z.eqb lo hi) with false in Hsafe by (symmetry; apply Z.eqb_neq; lia).
  destruct (Z.geb (find_addsub_prefix_160 ops lo hi) 0) eqn:Hadd_ge2.
  { apply Z.geb_le in Hadd_ge2; lia. }
  destruct (Z.geb (find_muldiv_prefix_160 ops lo hi) 0) eqn:Hmul_ge2.
  { apply Z.geb_le in Hmul_ge2; lia. }
  rewrite <- Hfind in Hsafe.
  replace (Z.geb idx 0) with true in Hsafe by (symmetry; apply Z.geb_le; lia).
  destruct Hsafe as [Hleft [Hright _]].
  pose proof (find_pow_left_prefix_bound_160 ops lo hi idx Hfind Hidx) as Hbound.
  rewrite (eval_range_fuel_safe_enough_gen_160 n n ops nums lo idx Hleft).
  2: { eapply sub_fuel_left_160; eauto. }
  2: { eapply sub_fuel_left_160; eauto. }
  rewrite (eval_range_fuel_safe_enough_gen_160 n n ops nums (idx + 1) hi Hright).
  2: { eapply sub_fuel_right_160; eauto. }
  2: { eapply sub_fuel_right_160; eauto. }
  reflexivity.
Qed.

Lemma eval_range_safe_addsub_apply_160 :
  forall ops nums lo hi idx,
    lo < hi ->
    0 <= idx ->
    idx = find_addsub_prefix_160 ops lo hi ->
    eval_range_safe_160 ops nums lo hi ->
    int_range_160
      (apply_code_160 (Znth idx ops 0)
        (eval_range_160 ops nums lo idx)
        (eval_range_160 ops nums (idx + 1) hi)).
Proof.
  intros ops nums lo hi idx Hlt Hidx Hfind Hsafe.
  unfold eval_range_safe_160, eval_range_160 in *.
  assert (0 < hi - lo + 1) by lia.
  destruct (Z.to_nat (hi - lo + 1)) eqn:Hfuel; [lia |].
  simpl in Hsafe.
  destruct Hsafe as [_ [_ [_ Hsafe]]].
  replace (Z.eqb lo hi) with false in Hsafe by (symmetry; apply Z.eqb_neq; lia).
  rewrite <- Hfind in Hsafe.
  replace (Z.geb idx 0) with true in Hsafe by (symmetry; apply Z.geb_le; lia).
  tauto.
Qed.

Lemma eval_range_safe_muldiv_apply_160 :
  forall ops nums lo hi idx,
    lo < hi ->
    0 <= idx ->
    find_addsub_prefix_160 ops lo hi < 0 ->
    idx = find_muldiv_prefix_160 ops lo hi ->
    eval_range_safe_160 ops nums lo hi ->
    int_range_160
      (apply_code_160 (Znth idx ops 0)
        (eval_range_160 ops nums lo idx)
        (eval_range_160 ops nums (idx + 1) hi)).
Proof.
  intros ops nums lo hi idx Hlt Hidx Hadd Hfind Hsafe.
  unfold eval_range_safe_160, eval_range_160 in *.
  assert (0 < hi - lo + 1) by lia.
  destruct (Z.to_nat (hi - lo + 1)) eqn:Hfuel; [lia |].
  simpl in Hsafe.
  destruct Hsafe as [_ [_ [_ Hsafe]]].
  replace (Z.eqb lo hi) with false in Hsafe by (symmetry; apply Z.eqb_neq; lia).
  destruct (Z.geb (find_addsub_prefix_160 ops lo hi) 0) eqn:Hadd_ge.
  { apply Z.geb_le in Hadd_ge; lia. }
  rewrite <- Hfind in Hsafe.
  replace (Z.geb idx 0) with true in Hsafe by (symmetry; apply Z.geb_le; lia).
  tauto.
Qed.

Lemma eval_range_safe_muldiv_divisor_160 :
  forall ops nums lo hi idx,
    lo < hi ->
    0 <= idx ->
    find_addsub_prefix_160 ops lo hi < 0 ->
    idx = find_muldiv_prefix_160 ops lo hi ->
    Znth idx ops 0 = 3 ->
    eval_range_safe_160 ops nums lo hi ->
    eval_range_160 ops nums (idx + 1) hi <> 0.
Proof.
  intros ops nums lo hi idx Hlt Hidx Hadd Hfind Hop Hsafe.
  unfold eval_range_safe_160, eval_range_160 in *.
  assert (0 < hi - lo + 1) by lia.
  destruct (Z.to_nat (hi - lo + 1)) eqn:Hfuel; [lia |].
  simpl in Hsafe.
  destruct Hsafe as [_ [_ [_ Hsafe]]].
  replace (Z.eqb lo hi) with false in Hsafe by (symmetry; apply Z.eqb_neq; lia).
  destruct (Z.geb (find_addsub_prefix_160 ops lo hi) 0) eqn:Hadd_ge.
  { apply Z.geb_le in Hadd_ge; lia. }
  rewrite <- Hfind in Hsafe.
  replace (Z.geb idx 0) with true in Hsafe by (symmetry; apply Z.geb_le; lia).
  tauto.
Qed.

Lemma eval_range_safe_muldiv_no_overflow_160 :
  forall ops nums lo hi idx,
    lo < hi ->
    0 <= idx ->
    find_addsub_prefix_160 ops lo hi < 0 ->
    idx = find_muldiv_prefix_160 ops lo hi ->
    Znth idx ops 0 = 3 ->
    eval_range_safe_160 ops nums lo hi ->
    eval_range_160 ops nums lo idx <> INT_MIN \/
    eval_range_160 ops nums (idx + 1) hi <> -1.
Proof.
  intros ops nums lo hi idx Hlt Hidx Hadd Hfind Hop Hsafe.
  unfold eval_range_safe_160, eval_range_160 in *.
  assert (0 < hi - lo + 1) by lia.
  destruct (Z.to_nat (hi - lo + 1)) eqn:Hfuel; [lia |].
  simpl in Hsafe.
  destruct Hsafe as [_ [_ [_ Hsafe]]].
  replace (Z.eqb lo hi) with false in Hsafe by (symmetry; apply Z.eqb_neq; lia).
  destruct (Z.geb (find_addsub_prefix_160 ops lo hi) 0) eqn:Hadd_ge.
  { apply Z.geb_le in Hadd_ge; lia. }
  rewrite <- Hfind in Hsafe.
  replace (Z.geb idx 0) with true in Hsafe by (symmetry; apply Z.geb_le; lia).
  tauto.
Qed.

Lemma eval_range_safe_pow_apply_160 :
  forall ops nums lo hi idx,
    lo < hi ->
    0 <= idx ->
    find_addsub_prefix_160 ops lo hi < 0 ->
    find_muldiv_prefix_160 ops lo hi < 0 ->
    idx = find_pow_left_prefix_160 ops lo hi ->
    eval_range_safe_160 ops nums lo hi ->
    int_range_160
      (apply_code_160 (Znth idx ops 0)
        (eval_range_160 ops nums lo idx)
        (eval_range_160 ops nums (idx + 1) hi)).
Proof.
  intros ops nums lo hi idx Hlt Hidx Hadd Hmul Hfind Hsafe.
  unfold eval_range_safe_160, eval_range_160 in *.
  assert (0 < hi - lo + 1) by lia.
  destruct (Z.to_nat (hi - lo + 1)) eqn:Hfuel; [lia |].
  simpl in Hsafe.
  destruct Hsafe as [_ [_ [_ Hsafe]]].
  replace (Z.eqb lo hi) with false in Hsafe by (symmetry; apply Z.eqb_neq; lia).
  destruct (Z.geb (find_addsub_prefix_160 ops lo hi) 0) eqn:Hadd_ge.
  { apply Z.geb_le in Hadd_ge; lia. }
  destruct (Z.geb (find_muldiv_prefix_160 ops lo hi) 0) eqn:Hmul_ge.
  { apply Z.geb_le in Hmul_ge; lia. }
  rewrite <- Hfind in Hsafe.
  replace (Z.geb idx 0) with true in Hsafe by (symmetry; apply Z.geb_le; lia).
  tauto.
Qed.

Lemma eval_range_safe_pow_info_160 :
  forall ops nums lo hi idx,
    lo < hi ->
    0 <= idx ->
    find_addsub_prefix_160 ops lo hi < 0 ->
    find_muldiv_prefix_160 ops lo hi < 0 ->
    idx = find_pow_left_prefix_160 ops lo hi ->
    eval_range_safe_160 ops nums lo hi ->
    0 <= eval_range_160 ops nums (idx + 1) hi /\
    eval_range_160 ops nums (idx + 1) hi < INT_MAX /\
    pow_prefix_safe_160
      (eval_range_160 ops nums lo idx)
      (eval_range_160 ops nums (idx + 1) hi).
Proof.
  intros ops nums lo hi idx Hlt Hidx Hadd Hmul Hfind Hsafe.
  unfold eval_range_safe_160, eval_range_160 in *.
  assert (0 < hi - lo + 1) by lia.
  destruct (Z.to_nat (hi - lo + 1)) eqn:Hfuel; [lia |].
  simpl in Hsafe.
  destruct Hsafe as [_ [_ [_ Hsafe]]].
  replace (Z.eqb lo hi) with false in Hsafe by (symmetry; apply Z.eqb_neq; lia).
  destruct (Z.geb (find_addsub_prefix_160 ops lo hi) 0) eqn:Hadd_ge.
  { apply Z.geb_le in Hadd_ge; lia. }
  destruct (Z.geb (find_muldiv_prefix_160 ops lo hi) 0) eqn:Hmul_ge.
  { apply Z.geb_le in Hmul_ge; lia. }
  rewrite <- Hfind in Hsafe.
  replace (Z.geb idx 0) with true in Hsafe by (symmetry; apply Z.geb_le; lia).
  tauto.
Qed.

Lemma problem_160_pre_z_operand_length_160 :
  forall rows operands n,
    problem_160_pre_z rows operands ->
    operator_rows_well_formed_160 rows n ->
    Zlength operands = n + 1.
Proof.
  intros rows operands n Hpre Hrows.
  unfold problem_160_pre_z, problem_160_pre, operator_string_160 in Hpre.
  rewrite list_ascii_of_string_string_of_ascii_list_160 in Hpre.
  destruct Hpre as [Hlen _].
  destruct Hrows as [Hrows_len _].
  rewrite Zlength_correct.
  rewrite <- Hlen.
  rewrite Nat2Z.inj_succ.
  unfold operator_chars_160.
  rewrite map_length.
  rewrite <- Zlength_correct.
  lia.
Qed.

Lemma operator_rows_payload_valid_160 :
  forall rows n i,
    operator_rows_well_formed_160 rows n ->
    0 <= i < n ->
    operator_payload_valid_160 (row_payload_z_160 (Znth i rows nil)).
Proof.
  intros rows n i Hrows Hi.
  destruct Hrows as [_ [_ Hvalid]].
  specialize (Hvalid i Hi).
  unfold operator_row_valid_160 in Hvalid.
  unfold operator_payload_valid_160.
  tauto.
Qed.

Lemma Zpow_160_0_r : forall base,
  Zpow_160 base 0 = 1.
Proof.
  reflexivity.
Qed.

Lemma Zpow_160_succ_r : forall base exp,
  0 <= exp ->
  Zpow_160 base (exp + 1) = Zpow_160 base exp * base.
Proof.
  intros base exp Hexp.
  unfold Zpow_160.
  replace (exp + 1) with (Z.succ exp) by lia.
  rewrite Z.pow_succ_r by lia.
  lia.
Qed.
End MigratedCompanionProofs.
Export MigratedCompanionProofs.
(* END migrated companion-spec proofs *)

Ltac solve_operator_payload_160 :=
  match goal with
  | H : operator_payload_valid_160 ?payload |- _ =>
      unfold operator_payload_valid_160 in H;
      destruct H as [_ [_ Hop]];
      repeat (destruct Hop as [Hop | Hop];
              [subst; unfold operator_code_payload_160, string_lib.c_string in *;
               repeat match goal with H : _ |- _ => progress (vm_compute in H) end;
               cbn; try congruence; try lia |]);
      subst; unfold operator_code_payload_160, string_lib.c_string in *;
      repeat match goal with H : _ |- _ => progress (vm_compute in H) end;
      cbn; try congruence; try lia
  end.

Ltac solve_pow_range_160 :=
  match goal with
  | Hsafe : pow_prefix_safe_160 ?base ?exp |- Zpow_160 ?base2 ?i * ?base3 <= _ =>
      replace (Zpow_160 base2 i * base3) with (Zpow_160 base i * base) by reflexivity;
      destruct Hsafe as [_ Hrange];
      pose proof (Hrange (i + 1) ltac:(lia)) as Hnext_range;
      rewrite Zpow_160_succ_r in Hnext_range by lia;
      unfold int_range_160 in Hnext_range;
      lia
  | Hsafe : pow_prefix_safe_160 ?base ?exp |- _ <= Zpow_160 ?base2 ?i * ?base3 =>
      replace (Zpow_160 base2 i * base3) with (Zpow_160 base i * base) by reflexivity;
      destruct Hsafe as [_ Hrange];
      pose proof (Hrange (i + 1) ltac:(lia)) as Hnext_range;
      rewrite Zpow_160_succ_r in Hnext_range by lia;
      unfold int_range_160 in Hnext_range;
      lia
  end.

Ltac solve_pow_succ_eq_160 :=
  match goal with
  | |- Zpow_160 ?base ?i * ?base = Zpow_160 ?base (?i + 1) =>
      rewrite Zpow_160_succ_r by lia;
      lia
  | Hres : ?result = Zpow_160 ?base ?i |- ?result * ?base = Zpow_160 ?base (?i + 1) =>
      rewrite Hres;
      rewrite Zpow_160_succ_r by lia;
      lia
  end.

Ltac solve_pow_return_160 :=
  match goal with
  | Hres : ?result = Zpow_160 ?base ?i |- ?result = Zpow_160 ?base ?exp =>
      rewrite Hres;
      replace i with exp by lia;
      reflexivity
  | |- Zpow_160 ?base ?i = Zpow_160 ?base ?exp =>
      replace i with exp by lia;
      reflexivity
  end.

Ltac split_safe_160 :=
  repeat match goal with
  | H : do_algebra_safe_160 _ _ |- _ =>
      unfold do_algebra_safe_160 in H; destruct H as [? [? [? ?]]]
  | H : eval_range_safe_160 _ _ _ _ |- _ =>
      unfold eval_range_safe_160 in H
  | H : eval_range_safe_fuel_160 (S _) _ _ _ _ |- _ =>
      simpl in H; destruct H as [? [? [? ?]]]
  | H : int_range_160 _ |- _ =>
      unfold int_range_160 in H
  end.

Ltac unfold_eval_160 :=
  unfold eval_range_160, eval_range_safe_160, apply_code_160,
    find_addsub_prefix_160, find_muldiv_prefix_160,
    find_pow_left_prefix_160 in *;
  cbn in *.

Ltac solve_find_prefix_160 :=
  repeat match goal with
  | |- context[find_addsub_prefix_160 ?ops ?lo ?lo] =>
      rewrite (find_addsub_prefix_base_160 ops lo)
  | |- context[find_muldiv_prefix_160 ?ops ?lo ?lo] =>
      rewrite (find_muldiv_prefix_base_160 ops lo)
  | |- context[find_pow_left_prefix_160 ?ops ?lo ?lo] =>
      rewrite (find_pow_left_prefix_base_160 ops lo)
  | H : Znth ?i ?ops 0 = 0 |- context[find_addsub_prefix_160 ?ops ?lo (?i + 1)] =>
      let Hhit := fresh "Hhit" in
      assert (Hhit : is_addsub_code_160 (Znth i ops 0) = true)
        by (unfold is_addsub_code_160; rewrite H; cbn; reflexivity);
      rewrite (find_addsub_prefix_succ_hit_160 ops lo i ltac:(lia) Hhit);
      clear Hhit
  | H : Znth ?i ?ops 0 = 1 |- context[find_addsub_prefix_160 ?ops ?lo (?i + 1)] =>
      let Hhit := fresh "Hhit" in
      assert (Hhit : is_addsub_code_160 (Znth i ops 0) = true)
        by (unfold is_addsub_code_160; rewrite H; cbn; reflexivity);
      rewrite (find_addsub_prefix_succ_hit_160 ops lo i ltac:(lia) Hhit);
      clear Hhit
  | H : Znth ?i ?ops 0 = 2 |- context[find_addsub_prefix_160 ?ops ?lo (?i + 1)] =>
      let Hmiss := fresh "Hmiss" in
      assert (Hmiss : is_addsub_code_160 (Znth i ops 0) = false)
        by (unfold is_addsub_code_160; rewrite H; cbn; reflexivity);
      rewrite (find_addsub_prefix_succ_miss_160 ops lo i ltac:(lia) Hmiss);
      clear Hmiss
  | H : Znth ?i ?ops 0 = 3 |- context[find_addsub_prefix_160 ?ops ?lo (?i + 1)] =>
      let Hmiss := fresh "Hmiss" in
      assert (Hmiss : is_addsub_code_160 (Znth i ops 0) = false)
        by (unfold is_addsub_code_160; rewrite H; cbn; reflexivity);
      rewrite (find_addsub_prefix_succ_miss_160 ops lo i ltac:(lia) Hmiss);
      clear Hmiss
  | H : Znth ?i ?ops 0 = 4 |- context[find_addsub_prefix_160 ?ops ?lo (?i + 1)] =>
      let Hmiss := fresh "Hmiss" in
      assert (Hmiss : is_addsub_code_160 (Znth i ops 0) = false)
        by (unfold is_addsub_code_160; rewrite H; cbn; reflexivity);
      rewrite (find_addsub_prefix_succ_miss_160 ops lo i ltac:(lia) Hmiss);
      clear Hmiss
  | H : Znth ?i ?ops 0 = 2 |- context[find_muldiv_prefix_160 ?ops ?lo (?i + 1)] =>
      let Hhit := fresh "Hhit" in
      assert (Hhit : is_muldiv_code_160 (Znth i ops 0) = true)
        by (unfold is_muldiv_code_160; rewrite H; cbn; reflexivity);
      rewrite (find_muldiv_prefix_succ_hit_160 ops lo i ltac:(lia) Hhit);
      clear Hhit
  | H : Znth ?i ?ops 0 = 3 |- context[find_muldiv_prefix_160 ?ops ?lo (?i + 1)] =>
      let Hhit := fresh "Hhit" in
      assert (Hhit : is_muldiv_code_160 (Znth i ops 0) = true)
        by (unfold is_muldiv_code_160; rewrite H; cbn; reflexivity);
      rewrite (find_muldiv_prefix_succ_hit_160 ops lo i ltac:(lia) Hhit);
      clear Hhit
  | H : Znth ?i ?ops 0 = 0 |- context[find_muldiv_prefix_160 ?ops ?lo (?i + 1)] =>
      let Hmiss := fresh "Hmiss" in
      assert (Hmiss : is_muldiv_code_160 (Znth i ops 0) = false)
        by (unfold is_muldiv_code_160; rewrite H; cbn; reflexivity);
      rewrite (find_muldiv_prefix_succ_miss_160 ops lo i ltac:(lia) Hmiss);
      clear Hmiss
  | H : Znth ?i ?ops 0 = 1 |- context[find_muldiv_prefix_160 ?ops ?lo (?i + 1)] =>
      let Hmiss := fresh "Hmiss" in
      assert (Hmiss : is_muldiv_code_160 (Znth i ops 0) = false)
        by (unfold is_muldiv_code_160; rewrite H; cbn; reflexivity);
      rewrite (find_muldiv_prefix_succ_miss_160 ops lo i ltac:(lia) Hmiss);
      clear Hmiss
  | H : Znth ?i ?ops 0 = 4 |- context[find_muldiv_prefix_160 ?ops ?lo (?i + 1)] =>
      let Hmiss := fresh "Hmiss" in
      assert (Hmiss : is_muldiv_code_160 (Znth i ops 0) = false)
        by (unfold is_muldiv_code_160; rewrite H; cbn; reflexivity);
      rewrite (find_muldiv_prefix_succ_miss_160 ops lo i ltac:(lia) Hmiss);
      clear Hmiss
  | Hprev : ?idx = find_pow_left_prefix_160 ?ops ?lo ?i,
    Hidx : ?idx = -1,
    Hop : Znth ?i ?ops 0 = 4
    |- context[find_pow_left_prefix_160 ?ops ?lo (?i + 1)] =>
      let Hhit := fresh "Hhit" in
      assert (Hhit : is_pow_code_160 (Znth i ops 0) = true)
        by (unfold is_pow_code_160; rewrite Hop; cbn; reflexivity);
      rewrite (find_pow_left_prefix_succ_first_160 ops lo i ltac:(lia) ltac:(lia) Hhit);
      clear Hhit
  | Hprev : ?idx = find_pow_left_prefix_160 ?ops ?lo ?i,
    Hidx : ?idx = -1,
    Hop : Znth ?i ?ops 0 = ?op
    |- context[find_pow_left_prefix_160 ?ops ?lo (?i + 1)] =>
      let Hmiss := fresh "Hmiss" in
      assert (Hmiss : is_pow_code_160 (Znth i ops 0) = false)
        by (unfold is_pow_code_160; rewrite Hop; cbn; try reflexivity; lia);
      rewrite (find_pow_left_prefix_succ_miss_160 ops lo i ltac:(lia) ltac:(lia) Hmiss);
      clear Hmiss
  | Hprev : ?idx = find_pow_left_prefix_160 ?ops ?lo ?i,
    Hidx : ?idx <> -1
    |- context[find_pow_left_prefix_160 ?ops ?lo (?i + 1)] =>
      rewrite (find_pow_left_prefix_succ_keep_160 ops lo i ltac:(lia) ltac:(lia))
  end.

Ltac solve_eval_apply_range_160 :=
  match goal with
  | Hsafe : eval_range_safe_160 ?ops ?nums ?lo ?hi,
    Hfind : ?idx = find_addsub_prefix_160 ?ops ?lo ?i,
    Hop : Znth ?idx ?ops 0 = ?op,
    Hlhs : ?lhs = eval_range_160 ?ops ?nums ?lo ?idx,
    Hrhs : ?rhs = eval_range_160 ?ops ?nums (?idx + 1) ?hi
    |- _ =>
      assert (i = hi) by lia; subst i;
      pose proof (eval_range_safe_addsub_apply_160 ops nums lo hi idx ltac:(lia) ltac:(lia) Hfind Hsafe) as Hr;
      rewrite Hop in Hr; unfold apply_code_160, int_range_160 in Hr;
      rewrite Hlhs, Hrhs in Hr;
      repeat (rewrite Z.eqb_refl in Hr || rewrite Z.eqb_neq in Hr by lia);
      cbn in Hr; lia
  | Hsafe : eval_range_safe_160 ?ops ?nums ?lo ?hi,
    Hadd : find_addsub_prefix_160 ?ops ?lo ?hi < 0,
    Hfind : ?idx = find_muldiv_prefix_160 ?ops ?lo ?i,
    Hop : Znth ?idx ?ops 0 = ?op,
    Hlhs : ?lhs = eval_range_160 ?ops ?nums ?lo ?idx,
    Hrhs : ?rhs = eval_range_160 ?ops ?nums (?idx + 1) ?hi
    |- _ =>
      assert (i = hi) by lia; subst i;
      pose proof (eval_range_safe_muldiv_apply_160 ops nums lo hi idx ltac:(lia) ltac:(lia) Hadd Hfind Hsafe) as Hr;
      rewrite Hop in Hr; unfold apply_code_160, int_range_160 in Hr;
      rewrite Hlhs, Hrhs in Hr;
      repeat (rewrite Z.eqb_refl in Hr || rewrite Z.eqb_neq in Hr by lia);
      cbn in Hr; lia
  | Hsafe : eval_range_safe_160 ?ops ?nums ?lo ?hi,
    Hadd : find_addsub_prefix_160 ?ops ?lo ?hi < 0,
    Hmul : find_muldiv_prefix_160 ?ops ?lo ?hi < 0,
    Hfind : ?idx = find_pow_left_prefix_160 ?ops ?lo ?i,
    Hop : Znth ?idx ?ops 0 = ?op,
    Hlhs : ?lhs = eval_range_160 ?ops ?nums ?lo ?idx,
    Hrhs : ?rhs = eval_range_160 ?ops ?nums (?idx + 1) ?hi
    |- _ =>
      assert (i = hi) by lia; subst i;
      pose proof (eval_range_safe_pow_apply_160 ops nums lo hi idx ltac:(lia) ltac:(lia) Hadd Hmul Hfind Hsafe) as Hr;
      rewrite Hop in Hr; unfold apply_code_160, int_range_160 in Hr;
      rewrite Hlhs, Hrhs in Hr;
      repeat (rewrite Z.eqb_refl in Hr || rewrite Z.eqb_neq in Hr by lia);
      cbn in Hr; lia
  end.

Ltac solve_eval_return_160 :=
  match goal with
  | Hsafe : eval_range_safe_160 ?ops ?nums ?lo ?hi,
    Hfind : ?idx = find_pow_left_prefix_160 ?ops ?lo ?i,
    Hadd : find_addsub_prefix_160 ?ops ?lo ?hi = -1,
    Hmul : find_muldiv_prefix_160 ?ops ?lo ?hi = -1,
    Hlhs : ?lhs = eval_range_160 ?ops ?nums ?lo ?idx,
    Hrhs : ?rhs = eval_range_160 ?ops ?nums (?idx + 1) ?hi,
    Hret : ?ret = Zpow_160 ?lhs ?rhs
    |- ?ret = eval_range_160 ?ops ?nums ?lo ?hi =>
      assert (i = hi) by lia; subst i;
      assert (Hfind_hi : idx = find_pow_left_prefix_160 ops lo hi) by exact Hfind;
      assert (Hop : Znth idx ops 0 = 4)
        by (eapply find_pow_left_prefix_hit_is_four_160; [exact Hfind_hi | lia]);
      rewrite Hret, Hlhs, Hrhs;
      rewrite (eval_range_pow_unfold_160 ops nums lo hi idx
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hfind_hi Hsafe);
      unfold apply_code_160; rewrite Hop; cbn; reflexivity
  | Hsafe : eval_range_safe_160 ?ops ?nums ?lo ?hi,
    Hfind : ?idx = find_muldiv_prefix_160 ?ops ?lo ?i,
    Hadd : find_addsub_prefix_160 ?ops ?lo ?hi = -1,
    Hlhs : ?lhs = eval_range_160 ?ops ?nums ?lo ?idx,
    Hrhs : ?rhs = eval_range_160 ?ops ?nums (?idx + 1) ?hi,
    Hop2 : Znth ?idx ?ops 0 <> 2
    |- Z.quot ?lhs ?rhs = eval_range_160 ?ops ?nums ?lo ?hi =>
      assert (i = hi) by lia; subst i;
      assert (Hfind_hi : idx = find_muldiv_prefix_160 ops lo hi) by exact Hfind;
      assert (Hop : Znth idx ops 0 = 3)
        by (eapply find_muldiv_prefix_not_two_is_three_160; [exact Hfind_hi | lia | exact Hop2]);
      rewrite Hlhs, Hrhs;
      rewrite (eval_range_muldiv_unfold_160 ops nums lo hi idx
        ltac:(lia) ltac:(lia) ltac:(lia) Hfind_hi Hsafe);
      unfold apply_code_160; rewrite Hop; cbn; reflexivity
  | Hsafe : eval_range_safe_160 ?ops ?nums ?lo ?hi,
    Hfind : ?idx = find_muldiv_prefix_160 ?ops ?lo ?i,
    Hadd : find_addsub_prefix_160 ?ops ?lo ?hi = -1,
    Hlhs : ?lhs = eval_range_160 ?ops ?nums ?lo ?idx,
    Hrhs : ?rhs = eval_range_160 ?ops ?nums (?idx + 1) ?hi,
    Hop : Znth ?idx ?ops 0 = 2
    |- ?lhs * ?rhs = eval_range_160 ?ops ?nums ?lo ?hi =>
      assert (i = hi) by lia; subst i;
      assert (Hfind_hi : idx = find_muldiv_prefix_160 ops lo hi) by exact Hfind;
      rewrite Hlhs, Hrhs;
      rewrite (eval_range_muldiv_unfold_160 ops nums lo hi idx
        ltac:(lia) ltac:(lia) ltac:(lia) Hfind_hi Hsafe);
      unfold apply_code_160; rewrite Hop; cbn; reflexivity
  | Hsafe : eval_range_safe_160 ?ops ?nums ?lo ?hi,
    Hfind : ?idx = find_addsub_prefix_160 ?ops ?lo ?i,
    Hlhs : ?lhs = eval_range_160 ?ops ?nums ?lo ?idx,
    Hrhs : ?rhs = eval_range_160 ?ops ?nums (?idx + 1) ?hi,
    Hop0 : Znth ?idx ?ops 0 <> 0
    |- ?lhs - ?rhs = eval_range_160 ?ops ?nums ?lo ?hi =>
      assert (i = hi) by lia; subst i;
      assert (Hfind_hi : idx = find_addsub_prefix_160 ops lo hi) by exact Hfind;
      assert (Hop : Znth idx ops 0 = 1)
        by (eapply find_addsub_prefix_nonzero_is_one_160; [exact Hfind_hi | lia | exact Hop0]);
      rewrite Hlhs, Hrhs;
      rewrite (eval_range_addsub_unfold_160 ops nums lo hi idx
        ltac:(lia) ltac:(lia) Hfind_hi Hsafe);
      unfold apply_code_160; rewrite Hop; cbn; reflexivity
  | Hsafe : eval_range_safe_160 ?ops ?nums ?lo ?hi,
    Hfind : ?idx = find_addsub_prefix_160 ?ops ?lo ?i,
    Hlhs : ?lhs = eval_range_160 ?ops ?nums ?lo ?idx,
    Hrhs : ?rhs = eval_range_160 ?ops ?nums (?idx + 1) ?hi,
    Hop : Znth ?idx ?ops 0 = 0
    |- ?lhs + ?rhs = eval_range_160 ?ops ?nums ?lo ?hi =>
      assert (i = hi) by lia; subst i;
      assert (Hfind_hi : idx = find_addsub_prefix_160 ops lo hi) by exact Hfind;
      rewrite Hlhs, Hrhs;
      rewrite (eval_range_addsub_unfold_160 ops nums lo hi idx
        ltac:(lia) ltac:(lia) Hfind_hi Hsafe);
      unfold apply_code_160; rewrite Hop; cbn; reflexivity
  | Hsafe : eval_range_safe_160 ?ops ?nums ?lo ?hi,
    Hfind : ?idx = find_pow_left_prefix_160 ?ops ?lo ?i,
    Hadd : find_addsub_prefix_160 ?ops ?lo ?hi = -1,
    Hmul : find_muldiv_prefix_160 ?ops ?lo ?hi = -1
    |- Zpow_160 (eval_range_160 ?ops ?nums ?lo ?idx)
         (eval_range_160 ?ops ?nums (?idx + 1) ?hi) =
       eval_range_160 ?ops ?nums ?lo ?hi =>
      assert (i = hi) by lia; subst i;
      assert (Hop : Znth idx ops 0 = 4)
        by (eapply find_pow_left_prefix_hit_is_four_160; [exact Hfind | lia]);
      rewrite (eval_range_pow_unfold_160 ops nums lo hi idx
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hfind Hsafe);
      unfold apply_code_160; rewrite Hop; cbn; reflexivity
  | Hsafe : eval_range_safe_160 ?ops ?nums ?lo ?hi,
    Hfind : ?idx = find_muldiv_prefix_160 ?ops ?lo ?i,
    Hadd : find_addsub_prefix_160 ?ops ?lo ?hi = -1,
    Hop2 : Znth ?idx ?ops 0 <> 2
    |- Z.quot (eval_range_160 ?ops ?nums ?lo ?idx)
         (eval_range_160 ?ops ?nums (?idx + 1) ?hi) =
       eval_range_160 ?ops ?nums ?lo ?hi =>
      assert (i = hi) by lia; subst i;
      assert (Hop : Znth idx ops 0 = 3)
        by (eapply find_muldiv_prefix_not_two_is_three_160; [exact Hfind | lia | exact Hop2]);
      rewrite (eval_range_muldiv_unfold_160 ops nums lo hi idx
        ltac:(lia) ltac:(lia) ltac:(lia) Hfind Hsafe);
      unfold apply_code_160; rewrite Hop; cbn; reflexivity
  | Hsafe : eval_range_safe_160 ?ops ?nums ?lo ?hi,
    Hfind : ?idx = find_muldiv_prefix_160 ?ops ?lo ?i,
    Hadd : find_addsub_prefix_160 ?ops ?lo ?hi = -1,
    Hop : Znth ?idx ?ops 0 = 2
    |- eval_range_160 ?ops ?nums ?lo ?idx *
       eval_range_160 ?ops ?nums (?idx + 1) ?hi =
       eval_range_160 ?ops ?nums ?lo ?hi =>
      assert (i = hi) by lia; subst i;
      rewrite (eval_range_muldiv_unfold_160 ops nums lo hi idx
        ltac:(lia) ltac:(lia) ltac:(lia) Hfind Hsafe);
      unfold apply_code_160; rewrite Hop; cbn; reflexivity
  | Hsafe : eval_range_safe_160 ?ops ?nums ?lo ?hi,
    Hfind : ?idx = find_addsub_prefix_160 ?ops ?lo ?i,
    Hop0 : Znth ?idx ?ops 0 <> 0
    |- eval_range_160 ?ops ?nums ?lo ?idx -
       eval_range_160 ?ops ?nums (?idx + 1) ?hi =
       eval_range_160 ?ops ?nums ?lo ?hi =>
      assert (i = hi) by lia; subst i;
      assert (Hop : Znth idx ops 0 = 1)
        by (eapply find_addsub_prefix_nonzero_is_one_160; [exact Hfind | lia | exact Hop0]);
      rewrite (eval_range_addsub_unfold_160 ops nums lo hi idx
        ltac:(lia) ltac:(lia) Hfind Hsafe);
      unfold apply_code_160; rewrite Hop; cbn; reflexivity
  | Hsafe : eval_range_safe_160 ?ops ?nums ?lo ?hi,
    Hfind : ?idx = find_addsub_prefix_160 ?ops ?lo ?i,
    Hop : Znth ?idx ?ops 0 = 0
    |- eval_range_160 ?ops ?nums ?lo ?idx +
       eval_range_160 ?ops ?nums (?idx + 1) ?hi =
       eval_range_160 ?ops ?nums ?lo ?hi =>
      assert (i = hi) by lia; subst i;
      rewrite (eval_range_addsub_unfold_160 ops nums lo hi idx
        ltac:(lia) ltac:(lia) Hfind Hsafe);
      unfold apply_code_160; rewrite Hop; cbn; reflexivity
  | |- Znth ?lo ?nums 0 = eval_range_160 ?ops ?nums ?lo ?hi =>
      rewrite (eval_range_base_160 ops nums lo);
      reflexivity
  end.

Ltac solve_eval_safe_subrange_160 :=
  match goal with
  | Hsafe : eval_range_safe_160 ?ops ?nums ?lo ?hi,
    Hfind : ?idx = find_addsub_prefix_160 ?ops ?lo ?i
    |- eval_range_safe_160 ?ops ?nums ?lo ?idx =>
      assert (i = hi) by lia; subst i;
      eapply eval_range_safe_addsub_left_160; [lia | lia | exact Hfind | exact Hsafe]
  | Hsafe : eval_range_safe_160 ?ops ?nums ?lo ?hi,
    Hfind : ?idx = find_addsub_prefix_160 ?ops ?lo ?i
    |- eval_range_safe_160 ?ops ?nums (?idx + 1) ?hi =>
      assert (i = hi) by lia; subst i;
      eapply eval_range_safe_addsub_right_160; [lia | lia | exact Hfind | exact Hsafe]
  | Hsafe : eval_range_safe_160 ?ops ?nums ?lo ?hi,
    Hadd : find_addsub_prefix_160 ?ops ?lo ?hi = -1,
    Hfind : ?idx = find_muldiv_prefix_160 ?ops ?lo ?i
    |- eval_range_safe_160 ?ops ?nums ?lo ?idx =>
      assert (i = hi) by lia; subst i;
      eapply eval_range_safe_muldiv_left_160; [lia | lia | lia | exact Hfind | exact Hsafe]
  | Hsafe : eval_range_safe_160 ?ops ?nums ?lo ?hi,
    Hadd : find_addsub_prefix_160 ?ops ?lo ?hi = -1,
    Hfind : ?idx = find_muldiv_prefix_160 ?ops ?lo ?i
    |- eval_range_safe_160 ?ops ?nums (?idx + 1) ?hi =>
      assert (i = hi) by lia; subst i;
      eapply eval_range_safe_muldiv_right_160; [lia | lia | lia | exact Hfind | exact Hsafe]
  | Hsafe : eval_range_safe_160 ?ops ?nums ?lo ?hi,
    Hadd : find_addsub_prefix_160 ?ops ?lo ?hi = -1,
    Hmul : find_muldiv_prefix_160 ?ops ?lo ?hi = -1,
    Hfind : ?idx = find_pow_left_prefix_160 ?ops ?lo ?i
    |- eval_range_safe_160 ?ops ?nums ?lo ?idx =>
      assert (i = hi) by lia; subst i;
      eapply eval_range_safe_pow_left_160; [lia | lia | lia | lia | exact Hfind | exact Hsafe]
  | Hsafe : eval_range_safe_160 ?ops ?nums ?lo ?hi,
    Hadd : find_addsub_prefix_160 ?ops ?lo ?hi = -1,
    Hmul : find_muldiv_prefix_160 ?ops ?lo ?hi = -1,
    Hfind : ?idx = find_pow_left_prefix_160 ?ops ?lo ?i
    |- eval_range_safe_160 ?ops ?nums (?idx + 1) ?hi =>
      assert (i = hi) by lia; subst i;
      eapply eval_range_safe_pow_right_160; [lia | lia | lia | lia | exact Hfind | exact Hsafe]
  end.

Ltac solve_160 :=
  pre_process_default;
  subst;
  solve_find_prefix_160;
  split_safe_160;
  try solve_operator_payload_160;
  try solve_pow_range_160;
  try solve_pow_succ_eq_160;
  try solve_pow_return_160;
  try solve_eval_apply_range_160;
  try solve_eval_return_160;
  try solve_eval_safe_subrange_160;
  first [
    Right; solve_find_prefix_160; entailer!
  | Left; solve_find_prefix_160; entailer!
  | entailer!
  ];
  solve_find_prefix_160;
  split_safe_160;
  try solve_operator_payload_160;
  try solve_pow_range_160;
  try solve_pow_succ_eq_160;
  try solve_pow_return_160;
  try solve_eval_apply_range_160;
  try solve_eval_return_160;
  try solve_eval_safe_subrange_160;
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H; subst
  | H : Z.eqb _ _ = false |- _ => apply Z.eqb_neq in H
  | H : (_ || _) = true |- _ => apply orb_true_iff in H; destruct H
  | H : (_ || _) = false |- _ => apply orb_false_iff in H; destruct H
  end;
  solve_find_prefix_160;
  try unfold_eval_160;
  try solve_eval_safe_subrange_160;
  try lia; try nia; try reflexivity; try congruence.

Lemma proof_of_operator_code_return_wit_1_split_goal_1 : operator_code_return_wit_1_split_goal_1.
Proof. solve_160. Qed.

Lemma proof_of_operator_code_return_wit_1 : operator_code_return_wit_1.
Proof. solve_160. Qed.
Lemma proof_of_operator_code_return_wit_2_split_goal_1 : operator_code_return_wit_2_split_goal_1.
Proof. solve_160. Qed.

Lemma proof_of_operator_code_return_wit_2 : operator_code_return_wit_2.
Proof. solve_160. Qed.
Lemma proof_of_operator_code_return_wit_3_split_goal_1 : operator_code_return_wit_3_split_goal_1.
Proof. solve_160. Qed.

Lemma proof_of_operator_code_return_wit_3 : operator_code_return_wit_3.
Proof. solve_160. Qed.
Lemma proof_of_operator_code_return_wit_4_split_goal_1 : operator_code_return_wit_4_split_goal_1.
Proof. solve_160. Qed.

Lemma proof_of_operator_code_return_wit_4 : operator_code_return_wit_4.
Proof. solve_160. Qed.
Lemma proof_of_operator_code_return_wit_5_split_goal_1 : operator_code_return_wit_5_split_goal_1.
Proof. solve_160. Qed.

Lemma proof_of_operator_code_return_wit_5 : operator_code_return_wit_5.
Proof. solve_160. Qed.
Lemma proof_of_int_pow_safety_wit_3_split_goal_1 : int_pow_safety_wit_3_split_goal_1.
Proof. solve_160. Qed.

Lemma proof_of_int_pow_safety_wit_3_split_goal_2 : int_pow_safety_wit_3_split_goal_2.
Proof. solve_160. Qed.

Lemma proof_of_int_pow_safety_wit_3 : int_pow_safety_wit_3.
Proof. solve_160. Qed.
Lemma proof_of_int_pow_entail_wit_1_split_goal_1 : int_pow_entail_wit_1_split_goal_1.
Proof. solve_160. Qed.

Lemma proof_of_int_pow_entail_wit_1 : int_pow_entail_wit_1.
Proof. solve_160. Qed.
Lemma proof_of_int_pow_entail_wit_2_split_goal_1 : int_pow_entail_wit_2_split_goal_1.
Proof. solve_160. Qed.

Lemma proof_of_int_pow_entail_wit_2 : int_pow_entail_wit_2.
Proof. solve_160. Qed.
Lemma proof_of_int_pow_return_wit_1_split_goal_1 : int_pow_return_wit_1_split_goal_1.
Proof. solve_160. Qed.

Lemma proof_of_int_pow_return_wit_1 : int_pow_return_wit_1.
Proof. solve_160. Qed.
Lemma proof_of_eval_range_safety_wit_22_split_goal_1 : eval_range_safety_wit_22_split_goal_1.
Proof.
  unfold eval_range_safety_wit_22_split_goal_1; intros.
  pre_process_default; entailer!.
  assert (i = hi_pre) by lia; subst i.
  pose proof (eval_range_safe_addsub_apply_160 ops_l nums_l lo_pre hi_pre idx ltac:(lia) ltac:(lia) PreH8 PreH17) as Hr.
  replace (Znth idx ops_l 0) with 0 in Hr by (symmetry; exact PreH1).
  unfold apply_code_160, int_range_160 in Hr.
  rewrite <- PreH3, <- PreH2 in Hr.
  cbn in Hr; lia.
Qed.

Lemma proof_of_eval_range_safety_wit_22_split_goal_2 : eval_range_safety_wit_22_split_goal_2.
Proof.
  unfold eval_range_safety_wit_22_split_goal_2; intros.
  pre_process_default; entailer!.
  assert (i = hi_pre) by lia; subst i.
  pose proof (eval_range_safe_addsub_apply_160 ops_l nums_l lo_pre hi_pre idx ltac:(lia) ltac:(lia) PreH8 PreH17) as Hr.
  replace (Znth idx ops_l 0) with 0 in Hr by (symmetry; exact PreH1).
  unfold apply_code_160, int_range_160 in Hr.
  rewrite <- PreH3, <- PreH2 in Hr.
  cbn in Hr; lia.
Qed.

Lemma proof_of_eval_range_safety_wit_22 : eval_range_safety_wit_22.
Proof.
  unfold eval_range_safety_wit_22; left; intros.
  pre_process_default; entailer!.
  all: assert (i = hi_pre) by lia; subst i;
       pose proof (eval_range_safe_addsub_apply_160 ops_l nums_l lo_pre hi_pre idx ltac:(lia) ltac:(lia) PreH8 PreH17) as Hr;
       replace (Znth idx ops_l 0) with 0 in Hr by (symmetry; exact PreH1);
       unfold apply_code_160, int_range_160 in Hr;
       rewrite <- PreH3, <- PreH2 in Hr;
       cbn in Hr; lia.
Qed.
Lemma proof_of_eval_range_safety_wit_23_split_goal_1 : eval_range_safety_wit_23_split_goal_1.
Proof.
  unfold eval_range_safety_wit_23_split_goal_1; intros.
  pre_process_default; entailer!.
  assert (i = hi_pre) by lia; subst i.
  pose proof (find_addsub_prefix_nonzero_is_one_160 ops_l lo_pre hi_pre idx PreH8 ltac:(lia) PreH1) as Hop.
  pose proof (eval_range_safe_addsub_apply_160 ops_l nums_l lo_pre hi_pre idx ltac:(lia) ltac:(lia) PreH8 PreH17) as Hr.
  replace (Znth idx ops_l 0) with 1 in Hr by (symmetry; exact Hop).
  unfold apply_code_160, int_range_160 in Hr.
  rewrite <- PreH3, <- PreH2 in Hr.
  cbn in Hr; lia.
Qed.

Lemma proof_of_eval_range_safety_wit_23_split_goal_2 : eval_range_safety_wit_23_split_goal_2.
Proof.
  unfold eval_range_safety_wit_23_split_goal_2; intros.
  pre_process_default; entailer!.
  assert (i = hi_pre) by lia; subst i.
  pose proof (find_addsub_prefix_nonzero_is_one_160 ops_l lo_pre hi_pre idx PreH8 ltac:(lia) PreH1) as Hop.
  pose proof (eval_range_safe_addsub_apply_160 ops_l nums_l lo_pre hi_pre idx ltac:(lia) ltac:(lia) PreH8 PreH17) as Hr.
  replace (Znth idx ops_l 0) with 1 in Hr by (symmetry; exact Hop).
  unfold apply_code_160, int_range_160 in Hr.
  rewrite <- PreH3, <- PreH2 in Hr.
  cbn in Hr; lia.
Qed.

Lemma proof_of_eval_range_safety_wit_23 : eval_range_safety_wit_23.
Proof.
  unfold eval_range_safety_wit_23; left; intros.
  pre_process_default; entailer!.
  all: assert (i = hi_pre) by lia; subst i;
       pose proof (find_addsub_prefix_nonzero_is_one_160 ops_l lo_pre hi_pre idx PreH8 ltac:(lia) PreH1) as Hop;
       pose proof (eval_range_safe_addsub_apply_160 ops_l nums_l lo_pre hi_pre idx ltac:(lia) ltac:(lia) PreH8 PreH17) as Hr;
       replace (Znth idx ops_l 0) with 1 in Hr by (symmetry; exact Hop);
       unfold apply_code_160, int_range_160 in Hr;
       rewrite <- PreH3, <- PreH2 in Hr;
       cbn in Hr; lia.
Qed.
Lemma proof_of_eval_range_safety_wit_45_split_goal_1 : eval_range_safety_wit_45_split_goal_1.
Proof.
  unfold eval_range_safety_wit_45_split_goal_1; intros.
  pre_process_default; entailer!.
  assert (i = hi_pre) by lia; subst i.
  pose proof (eval_range_safe_muldiv_apply_160 ops_l nums_l lo_pre hi_pre idx ltac:(lia) ltac:(lia) ltac:(lia) PreH8 PreH18) as Hr.
  replace (Znth idx ops_l 0) with 2 in Hr by (symmetry; exact PreH1).
  unfold apply_code_160, int_range_160 in Hr.
  rewrite <- PreH3, <- PreH2 in Hr.
  cbn in Hr; lia.
Qed.

Lemma proof_of_eval_range_safety_wit_45_split_goal_2 : eval_range_safety_wit_45_split_goal_2.
Proof.
  unfold eval_range_safety_wit_45_split_goal_2; intros.
  pre_process_default; entailer!.
  assert (i = hi_pre) by lia; subst i.
  pose proof (eval_range_safe_muldiv_apply_160 ops_l nums_l lo_pre hi_pre idx ltac:(lia) ltac:(lia) ltac:(lia) PreH8 PreH18) as Hr.
  replace (Znth idx ops_l 0) with 2 in Hr by (symmetry; exact PreH1).
  unfold apply_code_160, int_range_160 in Hr.
  rewrite <- PreH3, <- PreH2 in Hr.
  cbn in Hr; lia.
Qed.

Lemma proof_of_eval_range_safety_wit_45 : eval_range_safety_wit_45.
Proof.
  unfold eval_range_safety_wit_45; left; intros.
  pre_process_default; entailer!.
  all: assert (i = hi_pre) by lia; subst i;
       pose proof (eval_range_safe_muldiv_apply_160 ops_l nums_l lo_pre hi_pre idx ltac:(lia) ltac:(lia) ltac:(lia) PreH8 PreH18) as Hr;
       replace (Znth idx ops_l 0) with 2 in Hr by (symmetry; exact PreH1);
       unfold apply_code_160, int_range_160 in Hr;
       rewrite <- PreH3, <- PreH2 in Hr;
       cbn in Hr; lia.
Qed.
Lemma proof_of_eval_range_safety_wit_46_split_goal_1 : eval_range_safety_wit_46_split_goal_1.
Proof.
  unfold eval_range_safety_wit_46_split_goal_1; intros.
  pre_process_default; entailer!.
  assert (i = hi_pre) by lia; subst i.
  pose proof (find_muldiv_prefix_not_two_is_three_160 ops_l lo_pre hi_pre idx PreH8 ltac:(lia) PreH1) as Hop.
  pose proof (eval_range_safe_muldiv_no_overflow_160 ops_l nums_l lo_pre hi_pre idx ltac:(lia) ltac:(lia) ltac:(lia) PreH8 Hop PreH18) as Hno.
  rewrite <- PreH3, <- PreH2 in Hno.
  exact Hno.
Qed.

Lemma proof_of_eval_range_safety_wit_46_split_goal_2 : eval_range_safety_wit_46_split_goal_2.
Proof.
  unfold eval_range_safety_wit_46_split_goal_2; intros.
  pre_process_default; entailer!.
  assert (i = hi_pre) by lia; subst i.
  pose proof (find_muldiv_prefix_not_two_is_three_160 ops_l lo_pre hi_pre idx PreH8 ltac:(lia) PreH1) as Hop.
  pose proof (eval_range_safe_muldiv_divisor_160 ops_l nums_l lo_pre hi_pre idx ltac:(lia) ltac:(lia) ltac:(lia) PreH8 Hop PreH18) as Hnz.
  rewrite <- PreH2 in Hnz.
  exact Hnz.
Qed.

Lemma proof_of_eval_range_safety_wit_46 : eval_range_safety_wit_46.
Proof.
  unfold eval_range_safety_wit_46; left; intros.
  pre_process_default; entailer!.
  - assert (i = hi_pre) by lia; subst i.
    pose proof (find_muldiv_prefix_not_two_is_three_160 ops_l lo_pre hi_pre idx PreH8 ltac:(lia) PreH1) as Hop.
    pose proof (eval_range_safe_muldiv_divisor_160 ops_l nums_l lo_pre hi_pre idx ltac:(lia) ltac:(lia) ltac:(lia) PreH8 Hop PreH18) as Hnz.
    rewrite <- PreH2 in Hnz.
    exact Hnz.
  - assert (i = hi_pre) by lia; subst i.
    pose proof (find_muldiv_prefix_not_two_is_three_160 ops_l lo_pre hi_pre idx PreH8 ltac:(lia) PreH1) as Hop.
    pose proof (eval_range_safe_muldiv_no_overflow_160 ops_l nums_l lo_pre hi_pre idx ltac:(lia) ltac:(lia) ltac:(lia) PreH8 Hop PreH18) as Hno.
    rewrite <- PreH3, <- PreH2 in Hno.
    exact Hno.
Qed.
Lemma proof_of_eval_range_entail_wit_1 : eval_range_entail_wit_1.
Proof.
  unfold eval_range_entail_wit_1; intros.
  pre_process_default.
  Right.
  rewrite find_addsub_prefix_base_160.
  assert (lo_pre < hi_pre) by lia.
  entailer!.
Qed.
Lemma proof_of_eval_range_entail_wit_2_1 : eval_range_entail_wit_2_1.
Proof.
  unfold eval_range_entail_wit_2_1; intros.
  pre_process_default.
  Left.
  assert (Hhit : is_addsub_code_160 (Znth i ops_l 0) = true)
    by (unfold is_addsub_code_160; rewrite PreH1; cbn; reflexivity).
  rewrite (find_addsub_prefix_succ_hit_160 ops_l lo_pre i ltac:(lia) Hhit).
  entailer!.
Qed.
Lemma proof_of_eval_range_entail_wit_2_2 : eval_range_entail_wit_2_2.
Proof.
  unfold eval_range_entail_wit_2_2; intros.
  pre_process_default.
  Left.
  assert (Hhit : is_addsub_code_160 (Znth i ops_l 0) = true)
    by (unfold is_addsub_code_160; rewrite PreH1; cbn; reflexivity).
  rewrite (find_addsub_prefix_succ_hit_160 ops_l lo_pre i ltac:(lia) Hhit).
  entailer!.
Qed.
Lemma proof_of_eval_range_entail_wit_2_3 : eval_range_entail_wit_2_3.
Proof.
  unfold eval_range_entail_wit_2_3; intros.
  pre_process_default.
  Left.
  assert (Hhit : is_addsub_code_160 (Znth i ops_l 0) = true)
    by (unfold is_addsub_code_160; rewrite PreH1; cbn; reflexivity).
  rewrite (find_addsub_prefix_succ_hit_160 ops_l lo_pre i ltac:(lia) Hhit).
  entailer!.
Qed.
Lemma proof_of_eval_range_entail_wit_2_4 : eval_range_entail_wit_2_4.
Proof.
  unfold eval_range_entail_wit_2_4; intros.
  pre_process_default.
  Left.
  assert (Hhit : is_addsub_code_160 (Znth i ops_l 0) = true)
    by (unfold is_addsub_code_160; rewrite PreH1; cbn; reflexivity).
  rewrite (find_addsub_prefix_succ_hit_160 ops_l lo_pre i ltac:(lia) Hhit).
  entailer!.
Qed.
Lemma proof_of_eval_range_entail_wit_2_5 : eval_range_entail_wit_2_5.
Proof.
  unfold eval_range_entail_wit_2_5; intros.
  pre_process_default.
  Left.
  assert (Hmiss : is_addsub_code_160 (Znth i ops_l 0) = false).
  { unfold is_addsub_code_160. apply orb_false_iff; split; apply Z.eqb_neq; auto. }
  rewrite (find_addsub_prefix_succ_miss_160 ops_l lo_pre i ltac:(lia) Hmiss).
  rewrite <- PreH6.
  entailer!.
Qed.
Lemma proof_of_eval_range_entail_wit_2_6 : eval_range_entail_wit_2_6.
Proof.
  unfold eval_range_entail_wit_2_6; intros.
  pre_process_default.
  Right.
  assert (Hmiss : is_addsub_code_160 (Znth i ops_l 0) = false).
  { unfold is_addsub_code_160. apply orb_false_iff; split; apply Z.eqb_neq; auto. }
  rewrite (find_addsub_prefix_succ_miss_160 ops_l lo_pre i ltac:(lia) Hmiss).
  rewrite <- PreH6, PreH7.
  entailer!.
Qed.
Lemma proof_of_eval_range_entail_wit_3_split_goal_1 : eval_range_entail_wit_3_split_goal_1.
Proof.
  unfold eval_range_entail_wit_3_split_goal_1; intros.
  pre_process_default.
  assert (i = hi_pre) by lia; subst i.
  rewrite <- PreH5, PreH1.
  entailer!.
Qed.

Lemma proof_of_eval_range_entail_wit_3 : eval_range_entail_wit_3.
Proof.
  unfold eval_range_entail_wit_3; left; intros.
  pre_process_default.
  assert (i = hi_pre) by lia; subst i.
  rewrite <- PreH5, PreH1.
  entailer!.
Qed.
Lemma proof_of_eval_range_entail_wit_4 : eval_range_entail_wit_4.
Proof.
  unfold eval_range_entail_wit_4; intros.
  pre_process_default.
  Left.
  rewrite find_muldiv_prefix_base_160.
  entailer!.
Qed.
Lemma proof_of_eval_range_entail_wit_5_1 : eval_range_entail_wit_5_1.
Proof. solve_160. Qed.
Lemma proof_of_eval_range_entail_wit_5_2 : eval_range_entail_wit_5_2.
Proof. solve_160. Qed.
Lemma proof_of_eval_range_entail_wit_5_3 : eval_range_entail_wit_5_3.
Proof. solve_160. Qed.
Lemma proof_of_eval_range_entail_wit_5_4 : eval_range_entail_wit_5_4.
Proof. solve_160. Qed.
Lemma proof_of_eval_range_entail_wit_5_5 : eval_range_entail_wit_5_5.
Proof.
  unfold eval_range_entail_wit_5_5; intros.
  pre_process_default.
  Left.
  assert (Hmiss : is_muldiv_code_160 (Znth i ops_l 0) = false).
  { unfold is_muldiv_code_160. apply orb_false_iff; split; apply Z.eqb_neq; auto. }
  rewrite (find_muldiv_prefix_succ_miss_160 ops_l lo_pre i ltac:(lia) Hmiss).
  rewrite <- PreH6, PreH7.
  entailer!.
Qed.
Lemma proof_of_eval_range_entail_wit_5_6 : eval_range_entail_wit_5_6.
Proof.
  unfold eval_range_entail_wit_5_6; intros.
  pre_process_default.
  Right.
  assert (Hmiss : is_muldiv_code_160 (Znth i ops_l 0) = false).
  { unfold is_muldiv_code_160. apply orb_false_iff; split; apply Z.eqb_neq; auto. }
  rewrite (find_muldiv_prefix_succ_miss_160 ops_l lo_pre i ltac:(lia) Hmiss).
  rewrite <- PreH6.
  entailer!.
Qed.
Lemma proof_of_eval_range_entail_wit_6_split_goal_1 : eval_range_entail_wit_6_split_goal_1.
Proof.
  unfold eval_range_entail_wit_6_split_goal_1; intros.
  pre_process_default.
  assert (i = hi_pre) by lia; subst i.
  rewrite <- PreH5, PreH1.
  entailer!.
Qed.

Lemma proof_of_eval_range_entail_wit_6 : eval_range_entail_wit_6.
Proof.
  unfold eval_range_entail_wit_6; left; intros.
  pre_process_default.
  assert (i = hi_pre) by lia; subst i.
  rewrite <- PreH5, PreH1.
  entailer!.
Qed.
Lemma proof_of_eval_range_entail_wit_7 : eval_range_entail_wit_7.
Proof.
  unfold eval_range_entail_wit_7; intros.
  pre_process_default.
  Right.
  rewrite find_pow_left_prefix_base_160.
  entailer!.
Qed.
Lemma proof_of_eval_range_entail_wit_8_1 : eval_range_entail_wit_8_1.
Proof.
  unfold eval_range_entail_wit_8_1; intros.
  pre_process_default.
  Left.
  assert (Hhit : is_pow_code_160 (Znth i ops_l 0) = true)
    by (unfold is_pow_code_160; rewrite PreH1; cbn; reflexivity).
  rewrite (find_pow_left_prefix_succ_first_160 ops_l lo_pre i ltac:(lia) ltac:(lia) Hhit).
  entailer!.
Qed.
Lemma proof_of_eval_range_entail_wit_8_2 : eval_range_entail_wit_8_2.
Proof.
  unfold eval_range_entail_wit_8_2; intros.
  pre_process_default.
  Left.
  rewrite (find_pow_left_prefix_succ_keep_160 ops_l lo_pre i ltac:(lia) ltac:(lia)).
  rewrite <- PreH5.
  entailer!.
Qed.
Lemma proof_of_eval_range_entail_wit_8_3 : eval_range_entail_wit_8_3.
Proof.
  unfold eval_range_entail_wit_8_3; intros.
  pre_process_default.
  Right.
  assert (Hmiss : is_pow_code_160 (Znth i ops_l 0) = false)
    by (unfold is_pow_code_160; apply Z.eqb_neq; exact PreH1).
  rewrite (find_pow_left_prefix_succ_miss_160 ops_l lo_pre i ltac:(lia) ltac:(lia) Hmiss).
  rewrite PreH7.
  entailer!.
Qed.
Lemma proof_of_eval_range_return_wit_1_split_goal_1 : eval_range_return_wit_1_split_goal_1.
Proof.
  unfold eval_range_return_wit_1_split_goal_1; intros.
  pre_process_default; entailer!.
  assert (i = hi_pre) by lia; subst i.
  assert (Hpow : find_pow_left_prefix_160 ops_l lo_pre hi_pre = -1).
  { rewrite <- PreH5, PreH1. reflexivity. }
  rewrite (eval_range_no_operator_160 ops_l nums_l lo_pre hi_pre ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  reflexivity.
Qed.

Lemma proof_of_eval_range_return_wit_1 : eval_range_return_wit_1.
Proof.
  unfold eval_range_return_wit_1; left; intros.
  pre_process_default; entailer!.
  assert (i = hi_pre) by lia; subst i.
  assert (Hpow : find_pow_left_prefix_160 ops_l lo_pre hi_pre = -1).
  { rewrite <- PreH5, PreH1. reflexivity. }
  all: rewrite (eval_range_no_operator_160 ops_l nums_l lo_pre hi_pre ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia));
       reflexivity.
Qed.
Lemma proof_of_eval_range_return_wit_2_split_goal_1 : eval_range_return_wit_2_split_goal_1.
Proof.
  unfold eval_range_return_wit_2_split_goal_1; intros.
  pre_process_default; entailer!.
  assert (i = hi_pre) by lia; subst i.
  assert (Hfind : idx = find_pow_left_prefix_160 ops_l lo_pre hi_pre) by exact PreH8.
  assert (Hop : Znth idx ops_l 0 = 4).
  { eapply find_pow_left_prefix_hit_is_four_160; [exact Hfind | lia]. }
  rewrite PreH1, PreH2, PreH3.
  rewrite (eval_range_pow_unfold_160 ops_l nums_l lo_pre hi_pre idx
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hfind PreH19).
  unfold apply_code_160; rewrite Hop; cbn; reflexivity.
Qed.

Lemma proof_of_eval_range_return_wit_2 : eval_range_return_wit_2.
Proof.
  unfold eval_range_return_wit_2; left; intros.
  pre_process_default; entailer!.
  assert (i = hi_pre) by lia; subst i.
  assert (Hfind : idx = find_pow_left_prefix_160 ops_l lo_pre hi_pre) by exact PreH8.
  assert (Hop : Znth idx ops_l 0 = 4).
  { eapply find_pow_left_prefix_hit_is_four_160; [exact Hfind | lia]. }
  all: rewrite PreH1, PreH2, PreH3;
       rewrite (eval_range_pow_unfold_160 ops_l nums_l lo_pre hi_pre idx
         ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hfind PreH19);
       unfold apply_code_160; rewrite Hop; cbn; reflexivity.
Qed.
Lemma proof_of_eval_range_return_wit_3_split_goal_1 : eval_range_return_wit_3_split_goal_1.
Proof.
  unfold eval_range_return_wit_3_split_goal_1; intros.
  pre_process_default; entailer!.
  assert (i = hi_pre) by lia; subst i.
  assert (Hfind : idx = find_muldiv_prefix_160 ops_l lo_pre hi_pre) by exact PreH8.
  assert (Hop : Znth idx ops_l 0 = 3).
  { eapply find_muldiv_prefix_not_two_is_three_160; [exact Hfind | lia | exact PreH1]. }
  rewrite PreH2, PreH3.
  rewrite (eval_range_muldiv_unfold_160 ops_l nums_l lo_pre hi_pre idx
    ltac:(lia) ltac:(lia) ltac:(lia) Hfind PreH18).
  unfold apply_code_160; rewrite Hop; cbn; reflexivity.
Qed.

Lemma proof_of_eval_range_return_wit_3 : eval_range_return_wit_3.
Proof.
  unfold eval_range_return_wit_3; left; intros.
  pre_process_default; entailer!.
  assert (i = hi_pre) by lia; subst i.
  assert (Hfind : idx = find_muldiv_prefix_160 ops_l lo_pre hi_pre) by exact PreH8.
  assert (Hop : Znth idx ops_l 0 = 3).
  { eapply find_muldiv_prefix_not_two_is_three_160; [exact Hfind | lia | exact PreH1]. }
  all: rewrite PreH2, PreH3;
       rewrite (eval_range_muldiv_unfold_160 ops_l nums_l lo_pre hi_pre idx
         ltac:(lia) ltac:(lia) ltac:(lia) Hfind PreH18);
       unfold apply_code_160; rewrite Hop; cbn; reflexivity.
Qed.
Lemma proof_of_eval_range_return_wit_4_split_goal_1 : eval_range_return_wit_4_split_goal_1.
Proof.
  unfold eval_range_return_wit_4_split_goal_1; intros.
  pre_process_default; entailer!.
  assert (i = hi_pre) by lia; subst i.
  assert (Hfind : idx = find_muldiv_prefix_160 ops_l lo_pre hi_pre) by exact PreH8.
  rewrite PreH2, PreH3.
  rewrite (eval_range_muldiv_unfold_160 ops_l nums_l lo_pre hi_pre idx
    ltac:(lia) ltac:(lia) ltac:(lia) Hfind PreH18).
  unfold apply_code_160; rewrite PreH1; cbn; reflexivity.
Qed.

Lemma proof_of_eval_range_return_wit_4 : eval_range_return_wit_4.
Proof.
  unfold eval_range_return_wit_4; left; intros.
  pre_process_default; entailer!.
  assert (i = hi_pre) by lia; subst i.
  assert (Hfind : idx = find_muldiv_prefix_160 ops_l lo_pre hi_pre) by exact PreH8.
  all: rewrite PreH2, PreH3;
       rewrite (eval_range_muldiv_unfold_160 ops_l nums_l lo_pre hi_pre idx
         ltac:(lia) ltac:(lia) ltac:(lia) Hfind PreH18);
       unfold apply_code_160; rewrite PreH1; cbn; reflexivity.
Qed.
Lemma proof_of_eval_range_return_wit_5_split_goal_1 : eval_range_return_wit_5_split_goal_1.
Proof.
  unfold eval_range_return_wit_5_split_goal_1; intros.
  pre_process_default; entailer!.
  assert (i = hi_pre) by lia; subst i.
  assert (Hfind : idx = find_addsub_prefix_160 ops_l lo_pre hi_pre) by exact PreH8.
  assert (Hop : Znth idx ops_l 0 = 1).
  { eapply find_addsub_prefix_nonzero_is_one_160; [exact Hfind | lia | exact PreH1]. }
  rewrite PreH2, PreH3.
  rewrite (eval_range_addsub_unfold_160 ops_l nums_l lo_pre hi_pre idx
    ltac:(lia) ltac:(lia) Hfind PreH17).
  unfold apply_code_160; rewrite Hop; cbn; reflexivity.
Qed.

Lemma proof_of_eval_range_return_wit_5 : eval_range_return_wit_5.
Proof.
  unfold eval_range_return_wit_5; left; intros.
  pre_process_default; entailer!.
  assert (i = hi_pre) by lia; subst i.
  assert (Hfind : idx = find_addsub_prefix_160 ops_l lo_pre hi_pre) by exact PreH8.
  assert (Hop : Znth idx ops_l 0 = 1).
  { eapply find_addsub_prefix_nonzero_is_one_160; [exact Hfind | lia | exact PreH1]. }
  all: rewrite PreH2, PreH3;
       rewrite (eval_range_addsub_unfold_160 ops_l nums_l lo_pre hi_pre idx
         ltac:(lia) ltac:(lia) Hfind PreH17);
       unfold apply_code_160; rewrite Hop; cbn; reflexivity.
Qed.
Lemma proof_of_eval_range_return_wit_6_split_goal_1 : eval_range_return_wit_6_split_goal_1.
Proof.
  unfold eval_range_return_wit_6_split_goal_1; intros.
  pre_process_default; entailer!.
  assert (i = hi_pre) by lia; subst i.
  assert (Hfind : idx = find_addsub_prefix_160 ops_l lo_pre hi_pre) by exact PreH8.
  rewrite PreH2, PreH3.
  rewrite (eval_range_addsub_unfold_160 ops_l nums_l lo_pre hi_pre idx
    ltac:(lia) ltac:(lia) Hfind PreH17).
  unfold apply_code_160; rewrite PreH1; cbn; reflexivity.
Qed.

Lemma proof_of_eval_range_return_wit_6 : eval_range_return_wit_6.
Proof.
  unfold eval_range_return_wit_6; left; intros.
  pre_process_default; entailer!.
  assert (i = hi_pre) by lia; subst i.
  assert (Hfind : idx = find_addsub_prefix_160 ops_l lo_pre hi_pre) by exact PreH8.
  all: rewrite PreH2, PreH3;
       rewrite (eval_range_addsub_unfold_160 ops_l nums_l lo_pre hi_pre idx
         ltac:(lia) ltac:(lia) Hfind PreH17);
       unfold apply_code_160; rewrite PreH1; cbn; reflexivity.
Qed.
Lemma proof_of_eval_range_return_wit_7_split_goal_1 : eval_range_return_wit_7_split_goal_1.
Proof.
  unfold eval_range_return_wit_7_split_goal_1; intros.
  pre_process_default; entailer!.
  subst hi_pre.
  rewrite eval_range_base_160.
  reflexivity.
Qed.

Lemma proof_of_eval_range_return_wit_7 : eval_range_return_wit_7.
Proof.
  unfold eval_range_return_wit_7; left; intros.
  pre_process_default; entailer!.
  all: subst hi_pre; rewrite eval_range_base_160; reflexivity.
Qed.
Lemma proof_of_eval_range_partial_solve_wit_6_pure_split_goal_1 : eval_range_partial_solve_wit_6_pure_split_goal_1.
Proof.
  unfold eval_range_partial_solve_wit_6_pure_split_goal_1; intros.
  pre_process_default; entailer!.
  assert (i = hi_pre) by lia; subst i.
  eapply (eval_range_safe_addsub_left_160 ops_l nums_l lo_pre hi_pre idx);
    [lia | lia | exact PreH15 | exact PreH24].
Qed.

Lemma proof_of_eval_range_partial_solve_wit_6_pure : eval_range_partial_solve_wit_6_pure.
Proof.
  unfold eval_range_partial_solve_wit_6_pure; right; intros.
  pre_process_default; entailer!.
  assert (i = hi_pre) by lia; subst i.
  eapply (eval_range_safe_addsub_left_160 ops_l nums_l lo_pre hi_pre idx);
    [lia | lia | exact PreH15 | exact PreH24].
Qed.
Lemma proof_of_eval_range_partial_solve_wit_7_pure_split_goal_1 : eval_range_partial_solve_wit_7_pure_split_goal_1.
Proof.
  unfold eval_range_partial_solve_wit_7_pure_split_goal_1; intros.
  pre_process_default; entailer!.
  assert (i = hi_pre) by lia; subst i.
  eapply (eval_range_safe_addsub_right_160 ops_l nums_l lo_pre hi_pre idx);
    [lia | lia | exact PreH18 | exact PreH27].
Qed.

Lemma proof_of_eval_range_partial_solve_wit_7_pure : eval_range_partial_solve_wit_7_pure.
Proof.
  unfold eval_range_partial_solve_wit_7_pure; right; intros.
  pre_process_default; entailer!.
  assert (i = hi_pre) by lia; subst i.
  eapply (eval_range_safe_addsub_right_160 ops_l nums_l lo_pre hi_pre idx);
    [lia | lia | exact PreH18 | exact PreH27].
Qed.
Lemma proof_of_eval_range_partial_solve_wit_13_pure_split_goal_1 : eval_range_partial_solve_wit_13_pure_split_goal_1.
Proof.
  unfold eval_range_partial_solve_wit_13_pure_split_goal_1; intros.
  pre_process_default; entailer!.
  assert (i = hi_pre) by lia; subst i.
  eapply (eval_range_safe_muldiv_left_160 ops_l nums_l lo_pre hi_pre idx);
    [lia | lia | lia | exact PreH15 | exact PreH25].
Qed.

Lemma proof_of_eval_range_partial_solve_wit_13_pure : eval_range_partial_solve_wit_13_pure.
Proof.
  unfold eval_range_partial_solve_wit_13_pure; right; intros.
  pre_process_default; entailer!.
  assert (i = hi_pre) by lia; subst i.
  eapply (eval_range_safe_muldiv_left_160 ops_l nums_l lo_pre hi_pre idx);
    [lia | lia | lia | exact PreH15 | exact PreH25].
Qed.
Lemma proof_of_eval_range_partial_solve_wit_14_pure_split_goal_1 : eval_range_partial_solve_wit_14_pure_split_goal_1.
Proof.
  unfold eval_range_partial_solve_wit_14_pure_split_goal_1; intros.
  pre_process_default; entailer!.
  assert (i = hi_pre) by lia; subst i.
  eapply (eval_range_safe_muldiv_right_160 ops_l nums_l lo_pre hi_pre idx);
    [lia | lia | lia | exact PreH18 | exact PreH28].
Qed.

Lemma proof_of_eval_range_partial_solve_wit_14_pure : eval_range_partial_solve_wit_14_pure.
Proof.
  unfold eval_range_partial_solve_wit_14_pure; right; intros.
  pre_process_default; entailer!.
  assert (i = hi_pre) by lia; subst i.
  eapply (eval_range_safe_muldiv_right_160 ops_l nums_l lo_pre hi_pre idx);
    [lia | lia | lia | exact PreH18 | exact PreH28].
Qed.
Lemma proof_of_eval_range_partial_solve_wit_17_pure_split_goal_1 : eval_range_partial_solve_wit_17_pure_split_goal_1.
Proof.
  unfold eval_range_partial_solve_wit_17_pure_split_goal_1; intros.
  pre_process_default; entailer!.
  assert (i = hi_pre) by lia; subst i.
  eapply (eval_range_safe_pow_left_160 ops_l nums_l lo_pre hi_pre idx);
    [lia | lia | lia | lia | exact PreH15 | exact PreH26].
Qed.

Lemma proof_of_eval_range_partial_solve_wit_17_pure : eval_range_partial_solve_wit_17_pure.
Proof.
  unfold eval_range_partial_solve_wit_17_pure; right; intros.
  pre_process_default; entailer!.
  assert (i = hi_pre) by lia; subst i.
  eapply (eval_range_safe_pow_left_160 ops_l nums_l lo_pre hi_pre idx);
    [lia | lia | lia | lia | exact PreH15 | exact PreH26].
Qed.
Lemma proof_of_eval_range_partial_solve_wit_18_pure_split_goal_1 : eval_range_partial_solve_wit_18_pure_split_goal_1.
Proof.
  unfold eval_range_partial_solve_wit_18_pure_split_goal_1; intros.
  pre_process_default; entailer!.
  assert (i = hi_pre) by lia; subst i.
  eapply (eval_range_safe_pow_right_160 ops_l nums_l lo_pre hi_pre idx);
    [lia | lia | lia | lia | exact PreH18 | exact PreH29].
Qed.

Lemma proof_of_eval_range_partial_solve_wit_18_pure : eval_range_partial_solve_wit_18_pure.
Proof.
  unfold eval_range_partial_solve_wit_18_pure; right; intros.
  pre_process_default; entailer!.
  assert (i = hi_pre) by lia; subst i.
  eapply (eval_range_safe_pow_right_160 ops_l nums_l lo_pre hi_pre idx);
    [lia | lia | lia | lia | exact PreH18 | exact PreH29].
Qed.
Lemma proof_of_eval_range_partial_solve_wit_19_pure_split_goal_1 : eval_range_partial_solve_wit_19_pure_split_goal_1.
Proof.
  unfold eval_range_partial_solve_wit_19_pure_split_goal_1; intros.
  pre_process_default; entailer!.
  assert (i = hi_pre) by lia; subst i.
  pose proof (eval_range_safe_pow_info_160 ops_l nums_l lo_pre hi_pre idx
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PreH21 PreH32)
    as [Hnonneg [_ _]].
  rewrite PreH15.
  exact Hnonneg.
Qed.

Lemma proof_of_eval_range_partial_solve_wit_19_pure_split_goal_2 : eval_range_partial_solve_wit_19_pure_split_goal_2.
Proof.
  unfold eval_range_partial_solve_wit_19_pure_split_goal_2; intros.
  pre_process_default; entailer!.
  assert (i = hi_pre) by lia; subst i.
  pose proof (eval_range_safe_pow_info_160 ops_l nums_l lo_pre hi_pre idx
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PreH21 PreH32)
    as [_ [Hbound _]].
  rewrite PreH15.
  exact Hbound.
Qed.

Lemma proof_of_eval_range_partial_solve_wit_19_pure_split_goal_3 : eval_range_partial_solve_wit_19_pure_split_goal_3.
Proof.
  unfold eval_range_partial_solve_wit_19_pure_split_goal_3; intros.
  pre_process_default; entailer!.
  assert (i = hi_pre) by lia; subst i.
  pose proof (eval_range_safe_pow_info_160 ops_l nums_l lo_pre hi_pre idx
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PreH21 PreH32)
    as [_ [_ Hpow]].
  rewrite PreH16, PreH15.
  exact Hpow.
Qed.

Lemma proof_of_eval_range_partial_solve_wit_19_pure : eval_range_partial_solve_wit_19_pure.
Proof.
  unfold eval_range_partial_solve_wit_19_pure; right; intros.
  pre_process_default.
  assert (i = hi_pre) by lia; subst i.
  pose proof (eval_range_safe_pow_info_160 ops_l nums_l lo_pre hi_pre idx
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PreH21 PreH32)
    as [Hnonneg [Hbound Hpow]].
  entailer!.
  rewrite PreH16, PreH15; exact Hpow.
Qed.
Lemma proof_of_do_algebra_entail_wit_1_split_goal_1 : do_algebra_entail_wit_1_split_goal_1.
Proof. solve_160. Qed.

Lemma proof_of_do_algebra_entail_wit_1 : do_algebra_entail_wit_1.
Proof.
  unfold do_algebra_entail_wit_1; right; intros.
  pre_process_default; entailer!.
Qed.
Lemma proof_of_do_algebra_entail_wit_2_split_goal_1 : do_algebra_entail_wit_2_split_goal_1.
Proof.
  unfold do_algebra_entail_wit_2_split_goal_1; intros.
  pre_process_default; entailer!.
  eapply operator_rows_payload_valid_160; [exact PreH11 | lia].
Qed.

Lemma proof_of_do_algebra_entail_wit_2_split_goal_spatial : do_algebra_entail_wit_2_split_goal_spatial.
Proof.
  unfold do_algebra_entail_wit_2_split_goal_spatial; intros.
  rewrite (Znth_indep rows i __default__List_Z nil).
  - entailer!.
  - destruct PreH11 as [Hlen _].
    rewrite Hlen; lia.
Qed.

Lemma proof_of_do_algebra_entail_wit_2 : do_algebra_entail_wit_2.
Proof.
  unfold do_algebra_entail_wit_2; right; intros.
  pre_process_default; entailer!.
  - rewrite (Znth_indep rows i __default__List_Z nil).
    + entailer!.
    + destruct PreH11 as [Hlen _].
      rewrite Hlen; lia.
  - eapply operator_rows_payload_valid_160; [exact PreH11 | lia].
Qed.
Lemma proof_of_do_algebra_entail_wit_3_split_goal_spatial : do_algebra_entail_wit_3_split_goal_spatial.
Proof.
  unfold do_algebra_entail_wit_3_split_goal_spatial; intros.
  destruct PreH10 as [_ [_ Hrows_valid]].
  pose proof (Hrows_valid i ltac:(lia)) as Hrow.
  unfold operator_row_valid_160 in Hrow.
  destruct Hrow as [Hrow _].
  rewrite <- Hrow.
  replace (string_length (row_payload_z_160 (Znth i rows nil)) + 1) with
    (Zlength (Znth i rows nil)).
  2: {
    rewrite Hrow at 1.
    unfold string_lib.c_string, string_lib.string_length.
    rewrite Zlength_app_cons.
    reflexivity.
  }
  entailer!.
Qed.

Lemma proof_of_do_algebra_entail_wit_3 : do_algebra_entail_wit_3.
Proof.
  unfold do_algebra_entail_wit_3; right; intros.
  destruct PreH10 as [_ [_ Hrows_valid]].
  pose proof (Hrows_valid i ltac:(lia)) as Hrow.
  unfold operator_row_valid_160 in Hrow.
  destruct Hrow as [Hrow _].
  rewrite <- Hrow.
  replace (string_length (row_payload_z_160 (Znth i rows nil)) + 1) with
    (Zlength (Znth i rows nil)).
  2: {
    rewrite Hrow at 1.
    unfold string_lib.c_string, string_lib.string_length.
    rewrite Zlength_app_cons.
    reflexivity.
  }
  entailer!.
Qed.
Lemma proof_of_do_algebra_entail_wit_4_split_goal_1 : do_algebra_entail_wit_4_split_goal_1.
Proof.
  unfold do_algebra_entail_wit_4_split_goal_1; intros.
  pre_process_default; entailer!.
  rewrite PreH10, PreH1.
  apply operator_codes_prefix_snoc_160.
  destruct PreH11 as [Hlen _].
  lia.
Qed.

Lemma proof_of_do_algebra_entail_wit_4_split_goal_spatial : do_algebra_entail_wit_4_split_goal_spatial.
Proof.
  unfold do_algebra_entail_wit_4_split_goal_spatial; intros.
  pre_process_default.
  destruct PreH11 as [_ [_ Hrows_valid]].
  pose proof (Hrows_valid i ltac:(lia)) as Hrow_valid.
  unfold operator_row_valid_160 in Hrow_valid.
  destruct Hrow_valid as [Hrow _].
  replace (string_length (row_payload_z_160 (Znth i rows nil)) + 1) with
    (Zlength (Znth i rows nil)).
  2: {
    rewrite Hrow at 1.
    unfold string_lib.c_string, string_lib.string_length.
    rewrite Zlength_app_cons.
    reflexivity.
  }
  replace (c_string (row_payload_z_160 (Znth i rows nil))) with
    (Znth i rows nil) by exact Hrow.
  pose proof (CharPtrArray2.missing_i_merge_to_full
    operato_pre i operato_size_pre row_ptr rows (Znth i rows nil)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  change (CharPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth i rows nil)) (Znth i rows nil))
    with (CharArray.full row_ptr (Zlength (Znth i rows nil)) (Znth i rows nil)) in Hmerge.
  try rewrite sizeof_ptr.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  entailer!.
Qed.

Lemma proof_of_do_algebra_entail_wit_4 : do_algebra_entail_wit_4.
Proof.
  unfold do_algebra_entail_wit_4; right; intros.
  assert (Hirows : 0 <= i < Zlength rows).
  { destruct PreH11 as [Hlen _]. lia. }
  pre_process_default; entailer!.
  all: try (rewrite PreH10, PreH1; apply operator_codes_prefix_snoc_160; exact Hirows).
  destruct PreH11 as [_ [_ Hrows_valid]].
  pose proof (Hrows_valid i ltac:(lia)) as Hrow_valid.
  unfold operator_row_valid_160 in Hrow_valid.
  destruct Hrow_valid as [Hrow _].
  replace (string_length (row_payload_z_160 (Znth i rows nil)) + 1) with
    (Zlength (Znth i rows nil)).
  2: {
    rewrite Hrow at 1.
    unfold string_lib.c_string, string_lib.string_length.
    rewrite Zlength_app_cons.
    reflexivity.
  }
  replace (c_string (row_payload_z_160 (Znth i rows nil))) with
    (Znth i rows nil) by exact Hrow.
  pose proof (CharPtrArray2.missing_i_merge_to_full
    operato_pre i operato_size_pre row_ptr rows (Znth i rows nil)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  change (CharPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth i rows nil)) (Znth i rows nil))
    with (CharArray.full row_ptr (Zlength (Znth i rows nil)) (Znth i rows nil)) in Hmerge.
  try rewrite sizeof_ptr.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  entailer!.
Qed.
Lemma proof_of_do_algebra_entail_wit_5_split_goal_spatial : do_algebra_entail_wit_5_split_goal_spatial.
Proof.
  unfold do_algebra_entail_wit_5_split_goal_spatial; intros.
  assert (Hi : i = operato_size_pre) by lia.
  subst i.
  assert (Hcodes_len : Zlength (operator_codes_160 rows) = operato_size_pre).
  {
    destruct PreH10 as [Hrows_len _].
    unfold operator_codes_160.
    rewrite Zlength_map_160.
    exact Hrows_len.
  }
  rewrite PreH9.
  rewrite sublist_self by (symmetry; exact Hcodes_len).
  sep_apply (IntArray.seg_to_full ops 0 operato_size_pre (operator_codes_160 rows)).
  replace (ops + 0 * sizeof(INT)) with ops by lia.
  replace (operato_size_pre - 0) with operato_size_pre by lia.
  entailer!.
Qed.

Lemma proof_of_do_algebra_entail_wit_5 : do_algebra_entail_wit_5.
Proof.
  unfold do_algebra_entail_wit_5; left; intros.
  assert (Hi : i = operato_size_pre) by lia.
  subst i.
  assert (Hcodes_len : Zlength (operator_codes_160 rows) = operato_size_pre).
  {
    pose proof PreH10 as Hrows.
    destruct Hrows as [Hrows_len _].
    unfold operator_codes_160.
    rewrite Zlength_map_160.
    exact Hrows_len.
  }
  rewrite PreH9.
  rewrite sublist_self by (symmetry; exact Hcodes_len).
  pre_process_default; entailer!.
  sep_apply (IntArray.seg_to_full ops 0 operato_size_pre (operator_codes_160 rows)).
  replace (ops + 0 * sizeof(INT)) with ops by lia.
  replace (operato_size_pre - 0) with operato_size_pre by lia.
  rewrite IntArray.undef_seg_empty.
  entailer!.
Qed.
Lemma proof_of_do_algebra_return_wit_1_split_goal_1 : do_algebra_return_wit_1_split_goal_1.
Proof.
  unfold do_algebra_return_wit_1_split_goal_1; intros.
  pre_process_default; entailer!.
  unfold do_algebra_safe_160 in PreH8.
  destruct PreH8 as [_ [_ [_ Hspec]]].
  rewrite PreH1.
  replace (operand_size_pre - 1) with (Zlength operands - 1).
  - exact Hspec.
  - pose proof (problem_160_pre_z_operand_length_160
      rows operands operato_size_pre PreH7 PreH6) as Hlen.
    lia.
Qed.

Lemma proof_of_do_algebra_return_wit_1 : do_algebra_return_wit_1.
Proof.
  unfold do_algebra_return_wit_1; left; intros.
  pre_process_default; entailer!.
  unfold do_algebra_safe_160 in PreH8.
  destruct PreH8 as [_ [_ [_ Hspec]]].
  rewrite PreH1.
  replace (operand_size_pre - 1) with (Zlength operands - 1).
  - exact Hspec.
  - pose proof (problem_160_pre_z_operand_length_160
      rows operands operato_size_pre PreH7 PreH6) as Hlen.
    lia.
Qed.
Lemma proof_of_do_algebra_partial_solve_wit_4_pure_split_goal_1 : do_algebra_partial_solve_wit_4_pure_split_goal_1.
Proof.
  unfold do_algebra_partial_solve_wit_4_pure_split_goal_1; intros.
  pre_process_default; entailer!.
  destruct PreH10 as [Hrows_len _].
  unfold operator_codes_160.
  try rewrite Zlength_map_160.
  symmetry; exact Hrows_len.
Qed.

Lemma proof_of_do_algebra_partial_solve_wit_4_pure_split_goal_2 : do_algebra_partial_solve_wit_4_pure_split_goal_2.
Proof.
  unfold do_algebra_partial_solve_wit_4_pure_split_goal_2; intros.
  pre_process_default; entailer!.
  pose proof (problem_160_pre_z_operand_length_160
    rows operands operato_size_pre PreH11 PreH10) as Hlen.
  lia.
Qed.

Lemma proof_of_do_algebra_partial_solve_wit_4_pure_split_goal_3 : do_algebra_partial_solve_wit_4_pure_split_goal_3.
Proof.
  unfold do_algebra_partial_solve_wit_4_pure_split_goal_3; intros.
  pre_process_default; entailer!.
  unfold do_algebra_safe_160 in PreH12.
  destruct PreH12 as [_ [_ [Hsafe _]]].
  replace (operand_size_pre - 1) with (Zlength operands - 1).
  - exact Hsafe.
  - pose proof (problem_160_pre_z_operand_length_160
      rows operands operato_size_pre PreH11 PreH10) as Hlen.
    lia.
Qed.

Lemma proof_of_do_algebra_partial_solve_wit_4_pure : do_algebra_partial_solve_wit_4_pure.
Proof.
  unfold do_algebra_partial_solve_wit_4_pure; right; intros.
  pre_process_default; entailer!.
  - unfold do_algebra_safe_160 in PreH12.
    destruct PreH12 as [_ [_ [Hsafe _]]].
    replace (operand_size_pre - 1) with (Zlength operands - 1).
    + exact Hsafe.
    + pose proof (problem_160_pre_z_operand_length_160
        rows operands operato_size_pre PreH11 PreH10) as Hlen.
      lia.
  - pose proof (problem_160_pre_z_operand_length_160
      rows operands operato_size_pre PreH11 PreH10) as Hlen.
    lia.
  - destruct PreH10 as [Hrows_len _].
    unfold operator_codes_160.
    try rewrite Zlength_map_160.
    symmetry; exact Hrows_len.
Qed.
Lemma proof_of_do_algebra_partial_solve_wit_5_pure_split_goal_1 : do_algebra_partial_solve_wit_5_pure_split_goal_1.
Proof.
  unfold do_algebra_partial_solve_wit_5_pure_split_goal_1; intros.
  pre_process_default; entailer!.
  destruct PreH13 as [Hrows_len _].
  unfold operator_codes_160.
  try rewrite Zlength_map_160.
  symmetry; exact Hrows_len.
Qed.

Lemma proof_of_do_algebra_partial_solve_wit_5_pure : do_algebra_partial_solve_wit_5_pure.
Proof.
  unfold do_algebra_partial_solve_wit_5_pure; right; intros.
  pre_process_default; entailer!.
  destruct PreH13 as [Hrows_len _].
  unfold operator_codes_160.
  try rewrite Zlength_map_160.
  symmetry; exact Hrows_len.
Qed.
