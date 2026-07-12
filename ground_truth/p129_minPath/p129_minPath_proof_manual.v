Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Lia.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE Require Import p129_minPath_goal.
From SimpleC.EE Require Import p129_minPath_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p129_minPath.
Local Open Scope sac.
Local Open Scope bool_scope.
Local Open Scope list_scope.

Lemma find_one_scan_state_step_not_one_129 :
  forall rows n i j x y,
    0 <= i < n ->
    0 <= j < n ->
    find_one_scan_state_129 rows n i j x y ->
    Znth j (Znth i rows nil) 0 <> 1 ->
    find_one_scan_state_129 rows n i (j + 1) x y.
Proof.
  intros rows n i j x y Hi Hj Hscan Hneq.
  unfold find_one_scan_state_129 in *.
  destruct Hscan as [Hi_b [Hj_b [Hx_b [Hy_b Hcase]]]].
  repeat split; try lia.
  destruct Hcase as [Hfound | Hnone].
  - left; exact Hfound.
  - right.
    unfold no_one_before_129 in *.
    intros r c Hbefore.
    unfold scanned_before_129 in Hbefore.
    destruct Hbefore as [[Hr0 Hrn] [[Hc0 Hcn] Hpos]].
    destruct Hpos as [Hri | [Hri Hcj]].
    + apply Hnone.
      unfold scanned_before_129.
      repeat split; lia.
    + subst r.
      assert (c < j \/ c = j) as [Hclt | Hceq] by lia.
      * apply Hnone.
        unfold scanned_before_129.
        repeat split; lia.
      * subst c; exact Hneq.
Qed.

Lemma find_one_scan_state_finish_row_129 :
  forall rows n i j x y,
    0 <= i < n ->
    j >= n ->
    j <= n ->
    find_one_scan_state_129 rows n i j x y ->
    find_one_scan_state_129 rows n (i + 1) 0 x y.
Proof.
  intros rows n i j x y Hi Hj_ge Hj_le Hscan.
  unfold find_one_scan_state_129 in *.
  destruct Hscan as [Hi_b [Hj_b [Hx_b [Hy_b Hcase]]]].
  repeat split; try lia.
  destruct Hcase as [Hfound | Hnone].
  - left; exact Hfound.
  - right.
    unfold no_one_before_129 in *.
    intros r c Hbefore.
    apply Hnone.
    unfold scanned_before_129 in *.
    destruct Hbefore as [[Hr0 Hrn] [[Hc0 Hcn] Hpos]].
    repeat split; try lia.
Qed.

Lemma find_one_scan_state_found_129 :
  forall rows n i x y one_x one_y row_default,
    Zlength rows = n ->
    (forall r, 0 <= r < n -> Zlength (Znth r rows row_default) = n) ->
    0 <= one_x < n ->
    0 <= one_y < n ->
    Znth one_y (Znth one_x rows row_default) 0 = 1 ->
    i >= n ->
    i <= n ->
    find_one_scan_state_129 rows n i 0 x y ->
    find_one_state_129 rows n n 0 x y.
Proof.
  intros rows n i x y one_x one_y row_default Hlen Hrow Hox Hoy Hone Hi_ge Hi_le Hscan.
  unfold find_one_scan_state_129 in Hscan.
  unfold find_one_state_129, one_pos_z_129 in *.
  destruct Hscan as [Hi_b [_ [Hx_b [Hy_b Hcase]]]].
  repeat split; try lia.
  destruct Hcase as [Hfound | Hnone].
  - destruct Hfound as [_ [_ Heq]].
    exact Heq.
  - exfalso.
    assert (Hone_nil : Znth one_y (Znth one_x rows nil) 0 = 1).
    {
      rewrite (Znth_indep rows one_x nil row_default) by lia.
      exact Hone.
    }
    apply (Hnone one_x one_y).
    + unfold scanned_before_129.
      repeat split; try lia.
    + exact Hone_nil.
Qed.

Lemma output_prefix_snoc_129 :
  forall k minv i output v,
    output_prefix_129 k minv i output ->
    0 <= i < k ->
    v = output_value_129 i minv ->
    output_prefix_129 k minv (i + 1) (output ++ v :: nil).
Proof.
  intros k minv i output v Hprefix Hi Hv.
  unfold output_prefix_129 in *.
  destruct Hprefix as [Hi_b [Hlen Hnth]].
  split; [lia |].
  split.
  - rewrite Zlength_app. rewrite Hlen. change (Zlength (v :: nil)) with 1. lia.
  - intros t Ht.
    assert (t < i \/ t = i) as [Htlt | ->] by lia.
    + rewrite app_Znth1 by (rewrite Hlen; lia).
      apply Hnth; lia.
    + rewrite app_Znth2 by (rewrite Hlen; lia).
      rewrite Hlen.
      replace (i - i) with 0 by lia.
      change (Znth 0 (v :: nil) 0) with v.
      exact Hv.
Qed.

Lemma checked_neighbor_min_init_129 :
  forall rows n x y,
    2 <= n ->
    find_one_state_129 rows n n 0 x y ->
    checked_neighbor_min_129 rows n x y 0 (n * n).
Proof.
  intros rows n x y Hn Hfind.
  unfold checked_neighbor_min_129.
  unfold find_one_state_129 in Hfind.
  destruct Hfind as [_ [_ [Hx [Hy _]]]].
  repeat split; try lia.
Qed.

Lemma checked_neighbor_min_step_absent_129 :
  forall rows n x y stage minv,
    0 <= stage < 4 ->
    checked_neighbor_min_129 rows n x y stage minv ->
    (forall v, ~ dir_neighbor_value_129 rows n x y stage v) ->
    checked_neighbor_min_129 rows n x y (stage + 1) minv.
Proof.
  intros rows n x y stage minv Hstage Hchecked Habsent.
  unfold checked_neighbor_min_129 in *.
  destruct Hchecked as [Hstage_b [Hx [Hy [Hmin [Hle Hex]]]]].
  repeat split; try lia.
  - intros d v Hd Hdir.
    assert (d < stage \/ d = stage) as [Hdlt | ->] by lia.
    + apply (Hle d v); try lia; exact Hdir.
    + exfalso; apply (Habsent v); exact Hdir.
  - destruct Hex as [Hinit | [d [v [Hd [Hdir Heq]]]]].
    + left; exact Hinit.
    + right; exists d, v; repeat split; try lia; assumption.
Qed.

Lemma checked_neighbor_min_step_keep_129 :
  forall rows n x y stage minv v,
    0 <= stage < 4 ->
    checked_neighbor_min_129 rows n x y stage minv ->
    dir_neighbor_value_129 rows n x y stage v ->
    minv <= v ->
    checked_neighbor_min_129 rows n x y (stage + 1) minv.
Proof.
  intros rows n x y stage minv v Hstage Hchecked Hdir_stage Hcmp.
  unfold checked_neighbor_min_129 in *.
  destruct Hchecked as [Hstage_b [Hx [Hy [Hmin [Hle Hex]]]]].
  repeat split; try lia.
  - intros d w Hd Hdir.
    assert (d < stage \/ d = stage) as [Hdlt | ->] by lia.
    + apply (Hle d w); try lia; exact Hdir.
    + assert (w = v).
      {
        unfold dir_neighbor_value_129 in Hdir_stage, Hdir.
        repeat
          match goal with
          | H : _ \/ _ |- _ => destruct H as [H | H]
          | H : _ /\ _ |- _ => destruct H as [? H]
          end; try lia.
      }
      subst w; exact Hcmp.
  - destruct Hex as [Hinit | [d [w [Hd [Hdir Heq]]]]].
    + left; exact Hinit.
    + right; exists d, w; repeat split; try lia; assumption.
Qed.

Lemma checked_neighbor_min_step_update_129 :
  forall rows n x y stage minv v,
    0 <= stage < 4 ->
    checked_neighbor_min_129 rows n x y stage minv ->
    dir_neighbor_value_129 rows n x y stage v ->
    v < minv ->
    1 <= v <= n * n ->
    checked_neighbor_min_129 rows n x y (stage + 1) v.
Proof.
  intros rows n x y stage minv v Hstage Hchecked Hdir_stage Hcmp Hv.
  unfold checked_neighbor_min_129 in *.
  destruct Hchecked as [Hstage_b [Hx [Hy [Hmin [Hle Hex]]]]].
  repeat split; try lia.
  - intros d w Hd Hdir.
    assert (d < stage \/ d = stage) as [Hdlt | ->] by lia.
    + assert (minv <= w) by (apply (Hle d w); try lia; exact Hdir).
      lia.
    + assert (w = v).
      {
        unfold dir_neighbor_value_129 in Hdir_stage, Hdir.
        repeat
          match goal with
          | H : _ \/ _ |- _ => destruct H as [H | H]
          | H : _ /\ _ |- _ => destruct H as [? H]
          end; try lia.
      }
      subst w; lia.
  - right.
    exists stage, v.
    repeat split; try lia; assumption.
Qed.

Lemma Zlength_map_129 : forall {A B : Type} (f : A -> B) l,
  Zlength (map f l) = Zlength l.
Proof.
  intros.
  repeat rewrite Zlength_correct.
  rewrite map_length.
  reflexivity.
Qed.

Lemma length_of_Zlength_129 : forall {A : Type} (l : list A) n,
  0 <= n ->
  Zlength l = n ->
  length l = Z.to_nat n.
Proof.
  intros A l n Hn Hlen.
  apply Nat2Z.inj.
  rewrite Z2Nat.id by lia.
  rewrite <- Zlength_correct.
  lia.
Qed.

Lemma nth_map_Znth_129 :
  forall {A B : Type} (f : A -> B) (l : list A) i da db,
    0 <= i < Zlength l ->
    nth (Z.to_nat i) (map f l) db = f (Znth i l da).
Proof.
  intros A B f l i da db Hi.
  unfold Znth.
  transitivity (nth (Z.to_nat i) (map f l) (f da)).
  - apply nth_indep.
    rewrite map_length.
    rewrite Zlength_correct in Hi.
    lia.
  - rewrite (@map_nth A B f l da (Z.to_nat i)).
    reflexivity.
Qed.

Lemma nth_error_Znth_129 : forall {A : Type} (l : list A) i d,
  0 <= i < Zlength l ->
  nth_error l (Z.to_nat i) = Some (Znth i l d).
Proof.
  intros A l i d Hi.
  unfold Znth.
  apply nth_error_nth'.
  rewrite Zlength_correct in Hi.
  lia.
Qed.

Lemma nat_grid_length_129 : forall rows n,
  Zlength rows = n ->
  length (nat_grid_of_z_129 rows) = Z.to_nat n.
Proof.
  intros rows n Hlen.
  unfold nat_grid_of_z_129.
  rewrite map_length.
  apply length_of_Zlength_129.
  - rewrite <- Hlen. apply Zlength_nonneg.
  - exact Hlen.
Qed.

Lemma nat_grid_row_lengths_129 : forall rows n,
  (forall r, 0 <= r < Zlength rows -> Zlength (Znth r rows nil) = n) ->
  Forall (fun row : list nat => length row = Z.to_nat n)
         (nat_grid_of_z_129 rows).
Proof.
  induction rows as [| row rows IH]; intros n Hrow.
  - constructor.
  - unfold nat_grid_of_z_129; simpl.
    constructor.
    + unfold nat_row_of_z_129.
      rewrite map_length.
      assert (Hidx0 : 0 <= 0 < Zlength (row :: rows)).
      { rewrite Zlength_cons. pose proof (Zlength_nonneg rows). lia. }
      pose proof (Hrow 0 Hidx0) as Hrow0.
      change (Znth 0 (row :: rows) nil) with row in Hrow0.
      apply length_of_Zlength_129.
      * rewrite <- Hrow0. apply Zlength_nonneg.
      * exact Hrow0.
    + fold nat_grid_of_z_129.
      apply IH.
      intros r Hr.
      specialize (Hrow (r + 1)).
      assert (0 <= r + 1 < Zlength (row :: rows)) by (rewrite Zlength_cons; lia).
      specialize (Hrow H).
      rewrite Znth_cons in Hrow by lia.
      replace (r + 1 - 1) with r in Hrow by lia.
      exact Hrow.
Qed.

Lemma nat_grid_cell_129 :
  forall rows n r c,
    Zlength rows = n ->
    (forall r0, 0 <= r0 < n -> Zlength (Znth r0 rows nil) = n) ->
    0 <= r < n ->
    0 <= c < n ->
    grid_cell (nat_grid_of_z_129 rows) (Z.to_nat r) (Z.to_nat c) =
      Z.to_nat (Znth c (Znth r rows nil) 0).
Proof.
  intros rows n r c Hlen Hrow Hr Hc.
  unfold grid_cell, nat_grid_of_z_129, nat_row_of_z_129.
  rewrite (nth_map_Znth_129 (fun row => map Z.to_nat row) rows r nil nil).
  - rewrite (nth_map_Znth_129 Z.to_nat (Znth r rows nil) c 0 0%nat).
    + reflexivity.
    + rewrite Hrow by lia; lia.
  - rewrite Hlen; lia.
Qed.

Lemma Z_to_nat_pred_129 : forall x,
  0 < x ->
  (Z.to_nat x - 1)%nat = Z.to_nat (x - 1).
Proof.
  intros x Hx.
  rewrite Z2Nat.inj_sub by lia.
  simpl.
  reflexivity.
Qed.

Lemma Z_to_nat_succ_129 : forall x,
  0 <= x ->
  S (Z.to_nat x) = Z.to_nat (x + 1).
Proof.
  intros x Hx.
  replace (x + 1) with (Z.succ x) by lia.
  rewrite Z2Nat.inj_succ by lia.
  reflexivity.
Qed.

Lemma checked_neighbor_min_to_spec_129 :
  forall rows n x y minv,
    2 <= n ->
    Zlength rows = n ->
    (forall r, 0 <= r < n -> Zlength (Znth r rows nil) = n) ->
    (forall r c,
        0 <= r < n ->
        0 <= c < n ->
        1 <= Znth c (Znth r rows nil) 0 <= n * n) ->
    find_one_state_129 rows n n 0 x y ->
    checked_neighbor_min_129 rows n x y 4 minv ->
    is_neighbor_min_of_one (nat_grid_of_z_129 rows) (Z.to_nat minv).
Proof.
  intros rows n x y minv Hn Hlen Hrow Hrange Hfind Hchecked.
  unfold find_one_state_129, one_pos_z_129 in Hfind.
  destruct Hfind as [_ [_ [Hx [Hy [_ [_ Hone]]]]]].
  unfold checked_neighbor_min_129 in Hchecked.
  destruct Hchecked as [_ [_ [_ [Hmin [Hle Hex]]]]].
  exists (Z.to_nat n), (Z.to_nat x), (Z.to_nat y).
  repeat split.
  - apply nat_grid_length_129; exact Hlen.
  - apply nat_grid_row_lengths_129.
    intros r Hr.
    apply Hrow.
    rewrite Hlen in Hr.
    lia.
  - apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    rewrite Z2Nat.id by lia.
    lia.
  - apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    rewrite Z2Nat.id by lia.
    lia.
  - rewrite (nat_grid_cell_129 rows n x y Hlen Hrow Hx Hy).
    rewrite Hone.
    reflexivity.
  - destruct Hex as [Hinit | [d [v [Hd [Hdir Heq]]]]].
    + destruct (Z_lt_le_dec 0 x) as [Hxpos | Hxzero].
      * left.
        split.
        -- apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. simpl. lia.
        -- rewrite (Z_to_nat_pred_129 x Hxpos).
           rewrite (nat_grid_cell_129 rows n (x - 1) y Hlen Hrow ltac:(lia) Hy).
           assert (Hdir0 : dir_neighbor_value_129 rows n x y 0
                        (Znth y (Znth (x - 1) rows nil) 0)).
           { unfold dir_neighbor_value_129; left; repeat split; lia. }
           assert (minv <= Znth y (Znth (x - 1) rows nil) 0)
             by (apply (Hle 0); try lia; exact Hdir0).
           pose proof (Hrange (x - 1) y ltac:(lia) Hy).
           apply Nat2Z.inj.
           rewrite !Z2Nat.id by lia.
           lia.
      * right; left.
        split.
        -- apply Nat2Z.inj_lt.
           rewrite Nat2Z.inj_succ.
           rewrite !Z2Nat.id by lia.
           lia.
        -- rewrite (Z_to_nat_succ_129 x ltac:(lia)).
           rewrite (nat_grid_cell_129 rows n (x + 1) y Hlen Hrow ltac:(lia) Hy).
           assert (Hdir1 : dir_neighbor_value_129 rows n x y 1
                        (Znth y (Znth (x + 1) rows nil) 0)).
           { unfold dir_neighbor_value_129; right; left; repeat split; lia. }
           assert (minv <= Znth y (Znth (x + 1) rows nil) 0)
             by (apply (Hle 1); try lia; exact Hdir1).
           pose proof (Hrange (x + 1) y ltac:(lia) Hy).
           apply Nat2Z.inj.
           rewrite !Z2Nat.id by lia.
           lia.
    + unfold dir_neighbor_value_129 in Hdir.
      destruct Hdir as [[Hd0 [Hr0 [Hr1 [Hc Heqv]]]] |
        [[Hd0 [Hr0 [Hr1 [Hc Heqv]]]] |
        [[Hd0 [Hr0 [Hc0 [Hc1 Heqv]]]] |
         [Hd0 [Hr0 [Hc0 [Hc1 Heqv]]]]]]]; subst d minv.
      all: subst v.
      * left.
        split.
        -- apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. simpl. lia.
        -- rewrite (Z_to_nat_pred_129 x Hr0).
           rewrite (nat_grid_cell_129 rows n (x - 1) y Hlen Hrow ltac:(lia) Hc).
           reflexivity.
      * right; left.
        split.
        -- apply Nat2Z.inj_lt.
           rewrite Nat2Z.inj_succ.
           rewrite !Z2Nat.id by lia.
           lia.
        -- rewrite (Z_to_nat_succ_129 x Hr0).
           rewrite (nat_grid_cell_129 rows n (x + 1) y Hlen Hrow ltac:(lia) Hc).
           reflexivity.
      * right; right; left.
        split.
        -- apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. simpl. lia.
        -- rewrite (Z_to_nat_pred_129 y Hc0).
           rewrite (nat_grid_cell_129 rows n x (y - 1) Hlen Hrow Hr0 ltac:(lia)).
           reflexivity.
      * right; right; right.
        split.
        -- apply Nat2Z.inj_lt.
           rewrite Nat2Z.inj_succ.
           rewrite !Z2Nat.id by lia.
           lia.
        -- rewrite (Z_to_nat_succ_129 y Hc0).
           rewrite (nat_grid_cell_129 rows n x (y + 1) Hlen Hrow Hr0 ltac:(lia)).
           reflexivity.
  - intros Hxpos.
    assert (0 < x).
    { apply Nat2Z.inj_lt in Hxpos.
      rewrite Z2Nat.id in Hxpos by lia; simpl in Hxpos; lia. }
    rewrite (Z_to_nat_pred_129 x H).
    rewrite (nat_grid_cell_129 rows n (x - 1) y Hlen Hrow ltac:(lia) Hy).
    assert (Hdir : dir_neighbor_value_129 rows n x y 0
                  (Znth y (Znth (x - 1) rows nil) 0)).
    { unfold dir_neighbor_value_129; left; repeat split; lia. }
    assert (Hval := Hrange (x - 1) y ltac:(lia) Hy).
    apply Z2Nat.inj_le; try lia.
    apply (Hle 0); try lia; exact Hdir.
  - intros Hxsucc.
    assert (x + 1 < n).
    { apply Nat2Z.inj_lt in Hxsucc.
      rewrite Nat2Z.inj_succ in Hxsucc.
      rewrite !Z2Nat.id in Hxsucc by lia.
      lia. }
    rewrite (Z_to_nat_succ_129 x ltac:(lia)).
    rewrite (nat_grid_cell_129 rows n (x + 1) y Hlen Hrow ltac:(lia) Hy).
    assert (Hdir : dir_neighbor_value_129 rows n x y 1
                  (Znth y (Znth (x + 1) rows nil) 0)).
    { unfold dir_neighbor_value_129; right; left; repeat split; lia. }
    assert (Hval := Hrange (x + 1) y ltac:(lia) Hy).
    apply Z2Nat.inj_le; try lia.
    apply (Hle 1); try lia; exact Hdir.
  - intros Hypos.
    assert (0 < y).
    { apply Nat2Z.inj_lt in Hypos.
      rewrite Z2Nat.id in Hypos by lia; simpl in Hypos; lia. }
    rewrite (Z_to_nat_pred_129 y H).
    rewrite (nat_grid_cell_129 rows n x (y - 1) Hlen Hrow Hx ltac:(lia)).
    assert (Hdir : dir_neighbor_value_129 rows n x y 2
                  (Znth (y - 1) (Znth x rows nil) 0)).
    { unfold dir_neighbor_value_129; right; right; left; repeat split; lia. }
    assert (Hval := Hrange x (y - 1) Hx ltac:(lia)).
    apply Z2Nat.inj_le; try lia.
    apply (Hle 2); try lia; exact Hdir.
  - intros Hysucc.
    assert (y + 1 < n).
    { apply Nat2Z.inj_lt in Hysucc.
      rewrite Nat2Z.inj_succ in Hysucc.
      rewrite !Z2Nat.id in Hysucc by lia.
      lia. }
    rewrite (Z_to_nat_succ_129 y ltac:(lia)).
    rewrite (nat_grid_cell_129 rows n x (y + 1) Hlen Hrow Hx ltac:(lia)).
    assert (Hdir : dir_neighbor_value_129 rows n x y 3
                  (Znth (y + 1) (Znth x rows nil) 0)).
    { unfold dir_neighbor_value_129; right; right; right; repeat split; lia. }
    assert (Hval := Hrange x (y + 1) Hx ltac:(lia)).
    apply Z2Nat.inj_le; try lia.
    apply (Hle 3); try lia; exact Hdir.
Qed.

Lemma Z_even_of_nat_129 : forall n,
  Z.even (Z.of_nat n) = Nat.even n.
Proof.
  induction n.
  - reflexivity.
  - rewrite Nat.even_succ.
    rewrite <- Nat.negb_even.
    replace (Z.of_nat (S n)) with (Z.of_nat n + 1)%Z by lia.
    rewrite Z.even_add.
    simpl.
    rewrite IHn.
    destruct (Nat.even n); reflexivity.
Qed.

Lemma output_prefix_to_alternating_129 :
  forall k minv output,
    0 <= k ->
    output_prefix_129 k minv k output ->
    alternating_min_path_values (Z.to_nat k) (Z.to_nat minv)
      (nat_list_of_z_129 output).
Proof.
  intros k minv output Hk Hprefix.
  unfold output_prefix_129 in Hprefix.
  destruct Hprefix as [_ [Hlen Hnth]].
  unfold alternating_min_path_values, nat_list_of_z_129.
  split.
  - rewrite map_length.
    apply Nat2Z.inj.
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct.
    lia.
  - intros i Hi.
    assert (Ht : 0 <= Z.of_nat i < k).
    {
      split; [lia|].
      apply Nat2Z.inj_lt in Hi.
      rewrite Z2Nat.id in Hi by lia.
      exact Hi.
    }
    specialize (Hnth (Z.of_nat i) Ht).
    rewrite nth_error_map.
    replace i with (Z.to_nat (Z.of_nat i)) by lia.
    rewrite (nth_error_Znth_129 output (Z.of_nat i) 0).
    + rewrite Nat2Z.id.
      rewrite Hnth.
      unfold output_value_129.
      rewrite Z_even_of_nat_129.
      destruct (Nat.even i); reflexivity.
    + rewrite Hlen; exact Ht.
Qed.

Lemma min_neighbor_output_spec_129 :
  forall rows n x y minv k output,
    0 <= k ->
    min_neighbor_state_129 rows n x y minv ->
    output_prefix_129 k minv k output ->
    problem_129_spec_z rows k output.
Proof.
  intros rows n x y minv k output Hk Hstate Hprefix.
  unfold problem_129_spec_z.
  split; [exact Hk|].
  unfold problem_129_spec.
  destruct Hstate as [_ Hmin].
  exists (Z.to_nat minv).
  split.
  - exact Hmin.
  - apply output_prefix_to_alternating_129; assumption.
Qed.

Local Close Scope bool_scope.

Ltac c129_basic :=
  pre_process_default; try entailer!; try lia; try nia.



Lemma proof_of_minPath_safety_wit_9 : minPath_safety_wit_9.
Proof.
  c129_basic.
Qed.




Lemma proof_of_minPath_entail_wit_1 : minPath_entail_wit_1.
Proof.
  pre_process_default.
  unfold find_one_scan_state_129, no_one_before_129, scanned_before_129.
  entailer!.
  right.
  intros r c [[? ?] [? Hscan]].
  destruct Hscan as [? | [? ?]]; lia.
Qed.




Lemma proof_of_minPath_entail_wit_2 : minPath_entail_wit_2.
Proof.
  pre_process_default.
  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i
    grid_pre i n_pre rows).
  - dump_pre_spatial.
    lia.
  - Intros row_ptr.
    Exists row_ptr.
    rewrite (Znth_indep rows i nil __default__List_Z) by lia.
    unfold StorePtrAsElement.storeA.
    change (IntPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth i rows __default__List_Z))
      (Znth i rows __default__List_Z)) with
      (IntArray.full row_ptr (Zlength (Znth i rows __default__List_Z))
        (Znth i rows __default__List_Z)).
    entailer!.
    rewrite sizeof_ptr.
    cancel.
Qed.



Lemma proof_of_minPath_entail_wit_4_1 : minPath_entail_wit_4_1.
Proof.
  pre_process_default.
  Exists row_ptr_2.
  unfold find_one_scan_state_129, one_pos_z_129.
  entailer!.
Qed.



Lemma proof_of_minPath_entail_wit_4_2 : minPath_entail_wit_4_2.
Proof.
  pre_process_default.
  Exists row_ptr_2.
  entailer!.
  apply find_one_scan_state_step_not_one_129; try lia; assumption.
Qed.




Lemma proof_of_minPath_entail_wit_5 : minPath_entail_wit_5.
Proof.
  pre_process_default.
  pose proof (find_one_scan_state_finish_row_129
    rows n_pre i j x y ltac:(lia) ltac:(lia) ltac:(lia) PreH21)
    as Hscan_next.
  rewrite (Znth_indep rows i nil __default__List_Z) by lia.
  pose proof (IntPtrArray2.missing_i_merge_to_full
    grid_pre i n_pre row_ptr rows
    (Znth i rows __default__List_Z)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  rewrite sizeof_ptr.
  change (IntPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth i rows __default__List_Z))
    (Znth i rows __default__List_Z)) with
    (IntArray.full row_ptr (Zlength (Znth i rows __default__List_Z))
      (Znth i rows __default__List_Z)) in Hmerge.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  entailer!.
Qed.




Lemma proof_of_minPath_entail_wit_6 : minPath_entail_wit_6.
Proof.
  c129_basic.
Qed.





Lemma proof_of_minPath_entail_wit_7 : minPath_entail_wit_7.
Proof.
  pre_process_default.
  pose proof (find_one_scan_state_found_129
    rows n_pre i x y one_x one_y __default__List_Z
    PreH11 PreH13 ltac:(lia) ltac:(lia) PreH19
    ltac:(lia) ltac:(lia) PreH20) as Hfound.
  assert (i = n_pre) by lia; subst i.
  entailer!.
Qed.





Lemma proof_of_minPath_entail_wit_8 : minPath_entail_wit_8.
Proof.
  pre_process_default.
  pose proof (checked_neighbor_min_init_129 rows n_pre x y PreH1 PreH17) as Hchecked.
  entailer!.
Qed.

Lemma proof_of_minPath_entail_wit_9 : minPath_entail_wit_9.
Proof.
  pre_process_default.
  pose proof PreH14 as Hfind.
  unfold find_one_state_129, one_pos_z_129 in Hfind.
  destruct Hfind as [_ [_ [[Hx0 Hxn] [[Hy0 Hyn] _]]]].
  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i
    grid_pre (x - 1) n_pre rows).
  - dump_pre_spatial.
    lia.
  - Intros row_ptr.
    Exists row_ptr.
    rewrite (Znth_indep rows (x - 1) nil __default__List_Z) by lia.
    unfold StorePtrAsElement.storeA.
    change (IntPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth (x - 1) rows __default__List_Z))
      (Znth (x - 1) rows __default__List_Z)) with
      (IntArray.full row_ptr (Zlength (Znth (x - 1) rows __default__List_Z))
        (Znth (x - 1) rows __default__List_Z)).
    entailer!.
    rewrite sizeof_ptr.
    cancel.
Qed.




Lemma proof_of_minPath_entail_wit_10_1 : minPath_entail_wit_10_1.
Proof.
  pre_process_default.
  set (v := Znth y (Znth (x - 1) rows nil) 0).
  assert (Hdir : dir_neighbor_value_129 rows n_pre x y 0 v).
  {
    unfold v, dir_neighbor_value_129.
    left; repeat split; lia.
  }
  pose proof (checked_neighbor_min_step_keep_129
    rows n_pre x y 0 min v ltac:(lia) PreH20 Hdir ltac:(lia))
    as Hchecked.
  rewrite (Znth_indep rows (x - 1) nil __default__List_Z) by lia.
  pose proof (IntPtrArray2.missing_i_merge_to_full
    grid_pre (x - 1) n_pre row_ptr rows
    (Znth (x - 1) rows __default__List_Z)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  rewrite sizeof_ptr.
  change (IntPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth (x - 1) rows __default__List_Z))
    (Znth (x - 1) rows __default__List_Z)) with
    (IntArray.full row_ptr (Zlength (Znth (x - 1) rows __default__List_Z))
      (Znth (x - 1) rows __default__List_Z)) in Hmerge.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  entailer!.
Qed.





Lemma proof_of_minPath_entail_wit_10_2 : minPath_entail_wit_10_2.
Proof.
  pre_process_default.
  set (v := Znth y (Znth (x - 1) rows nil) 0).
  assert (Hdir : dir_neighbor_value_129 rows n_pre x y 0 v).
  {
    unfold v, dir_neighbor_value_129.
    left; repeat split; lia.
  }
  assert (Hv : 1 <= v <= n_pre * n_pre).
  {
    unfold v.
    rewrite (Znth_indep rows (x - 1) nil __default__List_Z) by lia.
    apply PreH17; repeat split; lia.
  }
  pose proof (checked_neighbor_min_step_update_129
    rows n_pre x y 0 min v ltac:(lia) PreH20 Hdir ltac:(lia) Hv)
    as Hchecked.
  rewrite (Znth_indep rows (x - 1) nil __default__List_Z) in * by lia.
  pose proof (IntPtrArray2.missing_i_merge_to_full
    grid_pre (x - 1) n_pre row_ptr rows
    (Znth (x - 1) rows __default__List_Z)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  rewrite sizeof_ptr.
  change (IntPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth (x - 1) rows __default__List_Z))
    (Znth (x - 1) rows __default__List_Z)) with
    (IntArray.full row_ptr (Zlength (Znth (x - 1) rows __default__List_Z))
      (Znth (x - 1) rows __default__List_Z)) in Hmerge.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  entailer!.
Qed.

Lemma proof_of_minPath_entail_wit_11_1 : minPath_entail_wit_11_1.
Proof.
  pre_process_default.
  assert (Habsent : forall v, ~ dir_neighbor_value_129 rows n_pre x y 0 v).
  {
    intros v Hdir.
    unfold dir_neighbor_value_129 in Hdir.
    repeat
      match goal with
      | H : _ \/ _ |- _ => destruct H as [H | H]
      | H : _ /\ _ |- _ => destruct H as [? H]
      end; lia.
  }
  pose proof (checked_neighbor_min_step_absent_129
    rows n_pre x y 0 min ltac:(lia) PreH16 Habsent) as Hchecked.
  pose proof PreH15 as Hfind.
  unfold find_one_state_129, one_pos_z_129 in Hfind.
  destruct Hfind as [_ [_ [[Hx0 Hxn] [[Hy0 Hyn] _]]]].
  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i
    grid_pre (x + 1) n_pre rows).
  - dump_pre_spatial.
    lia.
  - Intros row_ptr.
    Exists row_ptr.
    rewrite (Znth_indep rows (x + 1) nil __default__List_Z) by lia.
    unfold StorePtrAsElement.storeA.
    change (IntPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth (x + 1) rows __default__List_Z))
      (Znth (x + 1) rows __default__List_Z)) with
      (IntArray.full row_ptr (Zlength (Znth (x + 1) rows __default__List_Z))
        (Znth (x + 1) rows __default__List_Z)).
    entailer!.
    rewrite sizeof_ptr.
    cancel.
Qed.

Lemma proof_of_minPath_entail_wit_11_2 : minPath_entail_wit_11_2.
Proof.
  pre_process_default.
  pose proof PreH14 as Hfind.
  unfold find_one_state_129, one_pos_z_129 in Hfind.
  destruct Hfind as [_ [_ [[Hx0 Hxn] [[Hy0 Hyn] _]]]].
  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i
    grid_pre (x + 1) n_pre rows).
  - dump_pre_spatial.
    lia.
  - Intros row_ptr.
    Exists row_ptr.
    rewrite (Znth_indep rows (x + 1) nil __default__List_Z) by lia.
    unfold StorePtrAsElement.storeA.
    change (IntPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth (x + 1) rows __default__List_Z))
      (Znth (x + 1) rows __default__List_Z)) with
      (IntArray.full row_ptr (Zlength (Znth (x + 1) rows __default__List_Z))
        (Znth (x + 1) rows __default__List_Z)).
    entailer!.
    rewrite sizeof_ptr.
    cancel.
Qed.




Lemma proof_of_minPath_entail_wit_12_1 : minPath_entail_wit_12_1.
Proof.
  pre_process_default.
  set (v := Znth y (Znth (x + 1) rows nil) 0).
  assert (Hdir : dir_neighbor_value_129 rows n_pre x y 1 v).
  {
    unfold v, dir_neighbor_value_129.
    right; left; repeat split; lia.
  }
  pose proof (checked_neighbor_min_step_keep_129
    rows n_pre x y 1 min v ltac:(lia) PreH20 Hdir ltac:(lia))
    as Hchecked.
  rewrite (Znth_indep rows (x + 1) nil __default__List_Z) by lia.
  pose proof (IntPtrArray2.missing_i_merge_to_full
    grid_pre (x + 1) n_pre row_ptr rows
    (Znth (x + 1) rows __default__List_Z)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  rewrite sizeof_ptr.
  change (IntPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth (x + 1) rows __default__List_Z))
    (Znth (x + 1) rows __default__List_Z)) with
    (IntArray.full row_ptr (Zlength (Znth (x + 1) rows __default__List_Z))
      (Znth (x + 1) rows __default__List_Z)) in Hmerge.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  entailer!.
Qed.





Lemma proof_of_minPath_entail_wit_12_2 : minPath_entail_wit_12_2.
Proof.
  pre_process_default.
  set (v := Znth y (Znth (x + 1) rows nil) 0).
  assert (Hdir : dir_neighbor_value_129 rows n_pre x y 1 v).
  {
    unfold v, dir_neighbor_value_129.
    right; left; repeat split; lia.
  }
  assert (Hv : 1 <= v <= n_pre * n_pre).
  {
    unfold v.
    rewrite (Znth_indep rows (x + 1) nil __default__List_Z) by lia.
    apply PreH17; repeat split; lia.
  }
  pose proof (checked_neighbor_min_step_update_129
    rows n_pre x y 1 min v ltac:(lia) PreH20 Hdir ltac:(lia) Hv)
    as Hchecked.
  rewrite (Znth_indep rows (x + 1) nil __default__List_Z) in * by lia.
  pose proof (IntPtrArray2.missing_i_merge_to_full
    grid_pre (x + 1) n_pre row_ptr rows
    (Znth (x + 1) rows __default__List_Z)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  rewrite sizeof_ptr.
  change (IntPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth (x + 1) rows __default__List_Z))
    (Znth (x + 1) rows __default__List_Z)) with
    (IntArray.full row_ptr (Zlength (Znth (x + 1) rows __default__List_Z))
      (Znth (x + 1) rows __default__List_Z)) in Hmerge.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  entailer!.
Qed.

Lemma proof_of_minPath_entail_wit_13_1 : minPath_entail_wit_13_1.
Proof.
  pre_process_default.
  assert (Habsent : forall v, ~ dir_neighbor_value_129 rows n_pre x y 1 v).
  {
    intros v Hdir.
    unfold dir_neighbor_value_129 in Hdir.
    repeat
      match goal with
      | H : _ \/ _ |- _ => destruct H as [H | H]
      | H : _ /\ _ |- _ => destruct H as [? H]
      end; lia.
  }
  pose proof (checked_neighbor_min_step_absent_129
    rows n_pre x y 1 min ltac:(lia) PreH16 Habsent) as Hchecked.
  pose proof PreH15 as Hfind.
  unfold find_one_state_129, one_pos_z_129 in Hfind.
  destruct Hfind as [_ [_ [[Hx0 Hxn] [[Hy0 Hyn] _]]]].
  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i
    grid_pre x n_pre rows).
  - dump_pre_spatial.
    lia.
  - Intros row_ptr.
    Exists row_ptr.
    rewrite (Znth_indep rows x nil __default__List_Z) by lia.
    unfold StorePtrAsElement.storeA.
    change (IntPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth x rows __default__List_Z))
      (Znth x rows __default__List_Z)) with
      (IntArray.full row_ptr (Zlength (Znth x rows __default__List_Z))
        (Znth x rows __default__List_Z)).
    entailer!.
    rewrite sizeof_ptr.
    cancel.
Qed.

Lemma proof_of_minPath_entail_wit_13_2 : minPath_entail_wit_13_2.
Proof.
  pre_process_default.
  pose proof PreH14 as Hfind.
  unfold find_one_state_129, one_pos_z_129 in Hfind.
  destruct Hfind as [_ [_ [[Hx0 Hxn] [[Hy0 Hyn] _]]]].
  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i
    grid_pre x n_pre rows).
  - dump_pre_spatial.
    lia.
  - Intros row_ptr.
    Exists row_ptr.
    rewrite (Znth_indep rows x nil __default__List_Z) by lia.
    unfold StorePtrAsElement.storeA.
    change (IntPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth x rows __default__List_Z))
      (Znth x rows __default__List_Z)) with
      (IntArray.full row_ptr (Zlength (Znth x rows __default__List_Z))
        (Znth x rows __default__List_Z)).
    entailer!.
    rewrite sizeof_ptr.
    cancel.
Qed.




Lemma proof_of_minPath_entail_wit_14_1 : minPath_entail_wit_14_1.
Proof.
  pre_process_default.
  set (v := Znth (y - 1) (Znth x rows nil) 0).
  assert (Hdir : dir_neighbor_value_129 rows n_pre x y 2 v).
  {
    unfold v, dir_neighbor_value_129.
    right; right; left; repeat split; lia.
  }
  pose proof (checked_neighbor_min_step_keep_129
    rows n_pre x y 2 min v ltac:(lia) PreH20 Hdir ltac:(lia))
    as Hchecked.
  rewrite (Znth_indep rows x nil __default__List_Z) by lia.
  pose proof (IntPtrArray2.missing_i_merge_to_full
    grid_pre x n_pre row_ptr rows
    (Znth x rows __default__List_Z)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  rewrite sizeof_ptr.
  change (IntPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth x rows __default__List_Z))
    (Znth x rows __default__List_Z)) with
    (IntArray.full row_ptr (Zlength (Znth x rows __default__List_Z))
      (Znth x rows __default__List_Z)) in Hmerge.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  entailer!.
Qed.





Lemma proof_of_minPath_entail_wit_14_2 : minPath_entail_wit_14_2.
Proof.
  pre_process_default.
  set (v := Znth (y - 1) (Znth x rows nil) 0).
  assert (Hdir : dir_neighbor_value_129 rows n_pre x y 2 v).
  {
    unfold v, dir_neighbor_value_129.
    right; right; left; repeat split; lia.
  }
  assert (Hv : 1 <= v <= n_pre * n_pre).
  {
    unfold v.
    rewrite (Znth_indep rows x nil __default__List_Z) by lia.
    apply PreH17; repeat split; lia.
  }
  pose proof (checked_neighbor_min_step_update_129
    rows n_pre x y 2 min v ltac:(lia) PreH20 Hdir ltac:(lia) Hv)
    as Hchecked.
  rewrite (Znth_indep rows x nil __default__List_Z) in * by lia.
  pose proof (IntPtrArray2.missing_i_merge_to_full
    grid_pre x n_pre row_ptr rows
    (Znth x rows __default__List_Z)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  rewrite sizeof_ptr.
  change (IntPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth x rows __default__List_Z))
    (Znth x rows __default__List_Z)) with
    (IntArray.full row_ptr (Zlength (Znth x rows __default__List_Z))
      (Znth x rows __default__List_Z)) in Hmerge.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  entailer!.
Qed.

Lemma proof_of_minPath_entail_wit_15_1 : minPath_entail_wit_15_1.
Proof.
  pre_process_default.
  assert (Habsent1 : forall v, ~ dir_neighbor_value_129 rows n_pre x y 1 v).
  {
    intros v Hdir; unfold dir_neighbor_value_129 in Hdir.
    repeat match goal with
    | H : _ \/ _ |- _ => destruct H as [H | H]
    | H : _ /\ _ |- _ => destruct H as [? H]
    end; lia.
  }
  pose proof (checked_neighbor_min_step_absent_129
    rows n_pre x y 1 min ltac:(lia) PreH17 Habsent1) as Hchecked2.
  assert (Habsent2 : forall v, ~ dir_neighbor_value_129 rows n_pre x y 2 v).
  {
    intros v Hdir; unfold dir_neighbor_value_129 in Hdir.
    repeat match goal with
    | H : _ \/ _ |- _ => destruct H as [H | H]
    | H : _ /\ _ |- _ => destruct H as [? H]
    end; lia.
  }
  pose proof (checked_neighbor_min_step_absent_129
    rows n_pre x y 2 min ltac:(lia) Hchecked2 Habsent2) as Hchecked.
  pose proof PreH16 as Hfind.
  unfold find_one_state_129, one_pos_z_129 in Hfind.
  destruct Hfind as [_ [_ [[Hx0 Hxn] [[Hy0 Hyn] _]]]].
  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i grid_pre x n_pre rows).
  - dump_pre_spatial. lia.
  - Intros row_ptr.
    Exists row_ptr.
    rewrite (Znth_indep rows x nil __default__List_Z) by lia.
    unfold StorePtrAsElement.storeA.
    change (IntPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth x rows __default__List_Z))
      (Znth x rows __default__List_Z)) with
      (IntArray.full row_ptr (Zlength (Znth x rows __default__List_Z))
        (Znth x rows __default__List_Z)).
    entailer!.
    rewrite sizeof_ptr.
    cancel.
Qed.

Lemma proof_of_minPath_entail_wit_15_2 : minPath_entail_wit_15_2.
Proof.
  pre_process_default.
  assert (Habsent : forall v, ~ dir_neighbor_value_129 rows n_pre x y 2 v).
  {
    intros v Hdir; unfold dir_neighbor_value_129 in Hdir.
    repeat match goal with
    | H : _ \/ _ |- _ => destruct H as [H | H]
    | H : _ /\ _ |- _ => destruct H as [? H]
    end; lia.
  }
  pose proof (checked_neighbor_min_step_absent_129
    rows n_pre x y 2 min ltac:(lia) PreH16 Habsent) as Hchecked.
  pose proof PreH15 as Hfind.
  unfold find_one_state_129, one_pos_z_129 in Hfind.
  destruct Hfind as [_ [_ [[Hx0 Hxn] [[Hy0 Hyn] _]]]].
  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i grid_pre x n_pre rows).
  - dump_pre_spatial. lia.
  - Intros row_ptr.
    Exists row_ptr.
    rewrite (Znth_indep rows x nil __default__List_Z) by lia.
    unfold StorePtrAsElement.storeA.
    change (IntPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth x rows __default__List_Z))
      (Znth x rows __default__List_Z)) with
      (IntArray.full row_ptr (Zlength (Znth x rows __default__List_Z))
        (Znth x rows __default__List_Z)).
    entailer!.
    rewrite sizeof_ptr.
    cancel.
Qed.

Lemma proof_of_minPath_entail_wit_15_3 : minPath_entail_wit_15_3.
Proof.
  pre_process_default.
  pose proof PreH14 as Hfind.
  unfold find_one_state_129, one_pos_z_129 in Hfind.
  destruct Hfind as [_ [_ [[Hx0 Hxn] [[Hy0 Hyn] _]]]].
  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i grid_pre x n_pre rows).
  - dump_pre_spatial. lia.
  - Intros row_ptr.
    Exists row_ptr.
    rewrite (Znth_indep rows x nil __default__List_Z) by lia.
    unfold StorePtrAsElement.storeA.
    change (IntPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth x rows __default__List_Z))
      (Znth x rows __default__List_Z)) with
      (IntArray.full row_ptr (Zlength (Znth x rows __default__List_Z))
        (Znth x rows __default__List_Z)).
    entailer!.
    rewrite sizeof_ptr.
    cancel.
Qed.




Lemma proof_of_minPath_entail_wit_16_1 : minPath_entail_wit_16_1.
Proof.
  pre_process_default.
  set (v := Znth (y + 1) (Znth x rows nil) 0).
  assert (Hdir : dir_neighbor_value_129 rows n_pre x y 3 v).
  {
    unfold v, dir_neighbor_value_129.
    right; right; right; repeat split; lia.
  }
  pose proof (checked_neighbor_min_step_keep_129
    rows n_pre x y 3 min v ltac:(lia) PreH20 Hdir ltac:(lia))
    as Hchecked.
  rewrite (Znth_indep rows x nil __default__List_Z) by lia.
  pose proof (IntPtrArray2.missing_i_merge_to_full
    grid_pre x n_pre row_ptr rows
    (Znth x rows __default__List_Z)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  rewrite sizeof_ptr.
  change (IntPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth x rows __default__List_Z))
    (Znth x rows __default__List_Z)) with
    (IntArray.full row_ptr (Zlength (Znth x rows __default__List_Z))
      (Znth x rows __default__List_Z)) in Hmerge.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  entailer!.
Qed.





Lemma proof_of_minPath_entail_wit_16_2 : minPath_entail_wit_16_2.
Proof.
  pre_process_default.
  set (v := Znth (y + 1) (Znth x rows nil) 0).
  assert (Hdir : dir_neighbor_value_129 rows n_pre x y 3 v).
  {
    unfold v, dir_neighbor_value_129.
    right; right; right; repeat split; lia.
  }
  assert (Hv : 1 <= v <= n_pre * n_pre).
  {
    unfold v.
    rewrite (Znth_indep rows x nil __default__List_Z) by lia.
    apply PreH17; repeat split; lia.
  }
  pose proof (checked_neighbor_min_step_update_129
    rows n_pre x y 3 min v ltac:(lia) PreH20 Hdir ltac:(lia) Hv)
    as Hchecked.
  rewrite (Znth_indep rows x nil __default__List_Z) in * by lia.
  pose proof (IntPtrArray2.missing_i_merge_to_full
    grid_pre x n_pre row_ptr rows
    (Znth x rows __default__List_Z)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  rewrite sizeof_ptr.
  change (IntPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth x rows __default__List_Z))
    (Znth x rows __default__List_Z)) with
    (IntArray.full row_ptr (Zlength (Znth x rows __default__List_Z))
      (Znth x rows __default__List_Z)) in Hmerge.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  entailer!.
Qed.




Lemma proof_of_minPath_entail_wit_17_1 : minPath_entail_wit_17_1.
Proof.
  pre_process_default.
  assert (Habsent : forall v, ~ dir_neighbor_value_129 rows n_pre x y 3 v).
  {
    intros v Hdir; unfold dir_neighbor_value_129 in Hdir.
    repeat match goal with
    | H : _ \/ _ |- _ => destruct H as [H | H]
    | H : _ /\ _ |- _ => destruct H as [? H]
    end; lia.
  }
  pose proof (checked_neighbor_min_step_absent_129
    rows n_pre x y 3 min ltac:(lia) PreH15 Habsent) as Hchecked.
  assert (Hrow_nil :
    forall r, 0 <= r < n_pre -> Zlength (Znth r rows nil) = n_pre).
  {
    intros r Hr.
    rewrite (Znth_indep rows r nil __default__List_Z) by lia.
    apply PreH12; lia.
  }
  assert (Hrange_nil :
    forall r c, 0 <= r < n_pre -> 0 <= c < n_pre ->
      1 <= Znth c (Znth r rows nil) 0 <= n_pre * n_pre).
  {
    intros r c Hr Hc.
    rewrite (Znth_indep rows r nil __default__List_Z) by lia.
    apply PreH13; lia.
  }
  pose proof (checked_neighbor_min_to_spec_129
    rows n_pre x y min PreH2 PreH10 Hrow_nil Hrange_nil PreH14 Hchecked)
    as Hspec.
  unfold min_neighbor_state_129.
  entailer!.
Qed.



Lemma proof_of_minPath_entail_wit_17_2 : minPath_entail_wit_17_2.
Proof.
  pre_process_default.
  assert (Hrow_nil :
    forall r, 0 <= r < n_pre -> Zlength (Znth r rows nil) = n_pre).
  {
    intros r Hr.
    rewrite (Znth_indep rows r nil __default__List_Z) by lia.
    apply PreH11; lia.
  }
  assert (Hrange_nil :
    forall r c, 0 <= r < n_pre -> 0 <= c < n_pre ->
      1 <= Znth c (Znth r rows nil) 0 <= n_pre * n_pre).
  {
    intros r c Hr Hc.
    rewrite (Znth_indep rows r nil __default__List_Z) by lia.
    apply PreH12; lia.
  }
  pose proof (checked_neighbor_min_to_spec_129
    rows n_pre x y min PreH1 PreH9 Hrow_nil Hrange_nil PreH13 PreH14)
    as Hspec.
  unfold min_neighbor_state_129.
  entailer!.
Qed.


Lemma proof_of_minPath_entail_wit_18 : minPath_entail_wit_18.
Proof.
  pre_process_default.
  Exists (@nil Z).
  sep_apply IntArray.undef_full_to_undef_seg.
  rewrite IntArray.seg_empty.
  unfold output_prefix_129.
  entailer!.
Qed.


Lemma proof_of_minPath_entail_wit_19_1 : minPath_entail_wit_19_1.
Proof.
  pre_process_default.
  Exists (output_l_2 ++ 1 :: nil).
  assert (Hval : 1 = output_value_129 t min).
  {
    assert (Hmod : t mod 2 = 0).
    {
      rewrite <- Z.rem_mod_nonneg; lia.
    }
    unfold output_value_129.
    rewrite Zeven_mod.
    rewrite Hmod.
    reflexivity.
  }
  pose proof (output_prefix_snoc_129
    k_pre min t output_l_2 1 PreH14 ltac:(lia) Hval) as Hprefix.
  entailer!.
Qed.


Lemma proof_of_minPath_entail_wit_19_2 : minPath_entail_wit_19_2.
Proof.
  pre_process_default.
  Exists (output_l_2 ++ min :: nil).
  assert (Hmod : t mod 2 = 1).
  {
    pose proof (Z.mod_pos_bound t 2 ltac:(lia)).
    assert (t mod 2 <> 0).
    {
      intro Hzero.
      apply PreH1.
      rewrite Z.rem_mod_nonneg by lia.
      exact Hzero.
    }
    lia.
  }
  assert (Hval : min = output_value_129 t min).
  {
    unfold output_value_129.
    rewrite Zeven_mod.
    rewrite Hmod.
    reflexivity.
  }
  pose proof (output_prefix_snoc_129
    k_pre min t output_l_2 min PreH14 ltac:(lia) Hval) as Hprefix.
  entailer!.
Qed.

Lemma proof_of_minPath_return_wit_1 : minPath_return_wit_1.
Proof.
  pre_process_default.
  - assert (Ht_eq : t = k_pre) by lia.
    subst t.
    pose proof (min_neighbor_output_spec_129
      rows n_pre x y min k_pre output_l_2 ltac:(lia) PreH12 PreH13)
      as Hspec.
    Exists data_2 output_l_2 min.
    rewrite (IntArray.undef_seg_empty data_2 k_pre).
    sep_apply (IntArray.seg_to_full data_2 0 k_pre output_l_2).
    replace (data_2 + 0 * sizeof(INT)) with data_2 by lia.
    replace (k_pre - 0) with k_pre by lia.
    entailer!.
Qed.
