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
From SimpleC.EE Require Import p115_max_fill_goal.
From SimpleC.EE Require Import p115_max_fill_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p115_max_fill.
Local Open Scope sac.
Local Open Scope bool_scope.
Local Open Scope list_scope.

Lemma row_sum_prefix_z_0 : forall row,
  row_sum_prefix_z row 0 = 0.
Proof.
  intros row. unfold row_sum_prefix_z. reflexivity.
Qed.

Lemma sum_z_app : forall a b,
  sum_z (a ++ b) = sum_z a + sum_z b.
Proof.
  induction a as [| x xs IH]; intros b; simpl; [lia | rewrite IH; lia].
Qed.

Lemma firstn_succ_snoc_115 : forall {A : Type} n (l : list A) d,
  (n < List.length l)%nat ->
  firstn (S n) l = firstn n l ++ nth n l d :: nil.
Proof.
  induction n as [| n IH]; intros l d Hn.
  - destruct l; simpl in *; try lia. reflexivity.
  - destruct l; simpl in *; try lia.
    rewrite (IH l d) by lia. reflexivity.
Qed.

Lemma firstn_succ_Znth_115 : forall {A : Type} (l : list A) i d,
  0 <= i < Zlength l ->
  firstn (Z.to_nat (i + 1)) l =
  firstn (Z.to_nat i) l ++ Znth i l d :: nil.
Proof.
  intros A l i d Hi.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite firstn_succ_snoc_115 with (d := d) by (rewrite Zlength_correct in Hi; lia).
  reflexivity.
Qed.

Lemma row_sum_prefix_z_step : forall row j,
  0 <= j < Zlength row ->
  row_sum_prefix_z row (j + 1) =
  row_sum_prefix_z row j + Znth j row 0.
Proof.
  intros row j Hj.
  unfold row_sum_prefix_z.
  rewrite (firstn_succ_Znth_115 row j 0) by lia.
  rewrite sum_z_app. simpl. lia.
Qed.

Lemma row_sum_prefix_z_full : forall row n,
  Zlength row = n ->
  row_sum_prefix_z row n = sum_z row.
Proof.
  intros row n Hn.
  unfold row_sum_prefix_z.
  assert (Z.to_nat n = length row).
  { rewrite Zlength_correct in Hn. lia. }
  rewrite H.
  rewrite firstn_all.
  reflexivity.
Qed.

Lemma fold_left_Zadd_app : forall l x,
  fold_left Z.add l x = x + fold_left Z.add l 0.
Proof.
  induction l as [| a l IH]; intros x; simpl.
  - lia.
  - rewrite IH. rewrite (IH a). lia.
Qed.

Lemma trips_prefix_z_step : forall rows i capacity,
  0 <= i < Zlength rows ->
  trips_prefix_z rows (i + 1) capacity =
  trips_prefix_z rows i capacity + row_trip_z (Znth i rows nil) capacity.
Proof.
  intros rows i capacity Hi.
  unfold trips_prefix_z.
  rewrite (firstn_succ_Znth_115 rows i nil) by lia.
  rewrite map_app. simpl.
  rewrite fold_left_app. simpl.
  rewrite fold_left_Zadd_app. lia.
Qed.

Lemma row_trip_z_of_sum_prefix : forall row n capacity sum,
  Zlength row = n ->
  sum = row_sum_prefix_z row n ->
  row_trip_z row capacity =
  if Z.eqb sum 0 then 0 else Z.quot (sum - 1) capacity + 1.
Proof.
  intros row n capacity sum Hlen Hsum.
  unfold row_trip_z.
  rewrite <- (row_sum_prefix_z_full row n Hlen).
  subst sum. reflexivity.
Qed.

Lemma trips_prefix_z_step_from_sum : forall rows i n capacity sum,
  0 <= i < Zlength rows ->
  Zlength (Znth i rows nil) = n ->
  sum = row_sum_prefix_z (Znth i rows nil) n ->
  trips_prefix_z rows (i + 1) capacity =
  trips_prefix_z rows i capacity +
  (if Z.eqb sum 0 then 0 else Z.quot (sum - 1) capacity + 1).
Proof.
  intros rows i n capacity sum Hi Hlen Hsum.
  rewrite trips_prefix_z_step by lia.
  rewrite (row_trip_z_of_sum_prefix _ n _ sum Hlen Hsum).
  reflexivity.
Qed.

Lemma trips_prefix_z_nonneg_bound_step : forall i n capacity out ssum,
  0 <= i ->
  1 <= capacity ->
  0 <= n ->
  0 <= out <= i * n ->
  0 <= ssum <= n ->
  0 <= out + (if Z.eqb ssum 0 then 0 else Z.quot (ssum - 1) capacity + 1) <= (i + 1) * n.
Proof.
  intros i n capacity out ssum Hi Hcap Hn Hout Hsum.
  destruct (Z.eqb ssum 0) eqn:Hzero.
  - lia.
  - apply Z.eqb_neq in Hzero.
    assert (0 < ssum) by lia.
    assert (0 <= Z.quot (ssum - 1) capacity <= ssum - 1).
    { split.
      - apply Z.quot_pos; lia.
      - apply Z.quot_le_upper_bound; nia. }
    nia.
Qed.

Lemma fold_left_nat_add_start : forall l x,
  fold_left Nat.add l x = (x + fold_left Nat.add l 0)%nat.
Proof.
  induction l as [| a l IH]; intros x; simpl.
  - lia.
  - rewrite IH. rewrite (IH a). lia.
Qed.

Lemma sum_z_nat_row_of_z : forall row,
  (forall c, 0 <= c < Zlength row -> 0 <= Znth c row 0) ->
  Z.of_nat (fold_left Nat.add (nat_row_of_z row) 0%nat) = sum_z row.
Proof.
  induction row as [| x xs IH]; intros Hnonneg; simpl.
  - reflexivity.
  - assert (Hx : 0 <= x).
    { specialize (Hnonneg 0). simpl in Hnonneg. apply Hnonneg.
      rewrite Zlength_correct. simpl. lia. }
    assert (Hxs : forall c : Z, 0 <= c < Zlength xs -> 0 <= Znth c xs 0).
    { intros c Hc.
      specialize (Hnonneg (c + 1)).
      simpl in Hnonneg.
      rewrite Znth_cons in Hnonneg by lia.
      replace (c + 1 - 1) with c in Hnonneg by lia.
      apply Hnonneg. rewrite Zlength_correct in *. simpl in *. lia. }
    rewrite <- IH by exact Hxs.
    rewrite fold_left_nat_add_start.
    rewrite Nat2Z.inj_add.
    rewrite Z2Nat.id by lia.
    lia.
Qed.

Lemma nat_div_trip_bridge : forall s cap,
  0 <= s ->
  1 <= cap ->
  Z.of_nat ((Z.to_nat s + Z.to_nat cap - 1) / Z.to_nat cap)%nat =
  (if Z.eqb s 0 then 0 else Z.quot (s - 1) cap + 1).
Proof.
  intros s cap Hs Hcap.
  destruct (Z.eqb s 0) eqn:Hs0.
  - apply Z.eqb_eq in Hs0. subst s. simpl. rewrite Nat.div_small; lia.
  - apply Z.eqb_neq in Hs0.
    assert (Hspos : 0 < s) by lia.
    rewrite Nat2Z.inj_div by lia.
    rewrite Nat2Z.inj_sub by lia.
    rewrite Nat2Z.inj_add.
    rewrite !Z2Nat.id by lia.
    rewrite Z.quot_div_nonneg by lia.
    change (Z.of_nat 1) with 1.
    replace (cap + s - 1) with (s + cap - 1) by lia.
    replace ((s + cap - 1) / cap) with (1 + (s - 1) / cap).
    + rewrite Z.add_comm. reflexivity.
    + replace (s + cap - 1) with (1 * cap + (s - 1)) by lia.
      symmetry. apply Z.div_add_l. lia.
Qed.

Lemma row_trip_z_nat_bridge : forall row capacity,
  1 <= capacity ->
  (forall c, 0 <= c < Zlength row -> 0 <= Znth c row 0) ->
  Z.of_nat ((count_water (nat_row_of_z row) + Z.to_nat capacity - 1) /
    Z.to_nat capacity)%nat = row_trip_z row capacity.
Proof.
  intros row capacity Hcap Hnonneg.
  assert (Hsum : Z.of_nat (count_water (nat_row_of_z row)) = sum_z row).
  { unfold count_water. apply sum_z_nat_row_of_z. exact Hnonneg. }
  assert (Hsum_nonneg : 0 <= sum_z row) by lia.
  replace (count_water (nat_row_of_z row)) with (Z.to_nat (sum_z row)).
  2:{ apply Nat2Z.inj.
      rewrite Hsum. rewrite Z2Nat.id by lia. reflexivity. }
  unfold row_trip_z.
  rewrite nat_div_trip_bridge; try lia.
Qed.

Lemma required_trips_bridge_acc : forall rows capacity acc_nat acc_z,
  1 <= capacity ->
  Z.of_nat acc_nat = acc_z ->
  (forall r c, 0 <= r < Zlength rows ->
    0 <= c < Zlength (Znth r rows nil) ->
    0 <= Znth c (Znth r rows nil) 0) ->
  Z.of_nat
    (fold_left
      (fun acc well => (acc + (count_water well + Z.to_nat capacity - 1) /
        Z.to_nat capacity)%nat)
      (nat_grid_of_z rows)
      acc_nat) =
  fold_left Z.add (map (fun row => row_trip_z row capacity) rows) acc_z.
Proof.
  induction rows as [| row rest IH]; intros capacity acc_nat acc_z Hcap Hacc Hnonneg.
  - simpl. exact Hacc.
  - simpl.
    assert (Hacc' :
      Z.of_nat
        (acc_nat + (count_water (nat_row_of_z row) + Z.to_nat capacity - 1) /
         Z.to_nat capacity)%nat =
      acc_z + row_trip_z row capacity).
    { rewrite Nat2Z.inj_add.
      rewrite Hacc.
      rewrite row_trip_z_nat_bridge; try lia.
      intros c Hc. apply (Hnonneg 0 c).
      - rewrite Zlength_correct. simpl. lia.
      - exact Hc. }
    assert (Htail : forall r c : Z,
      0 <= r < Zlength rest ->
      0 <= c < Zlength (Znth r rest nil) ->
      0 <= Znth c (Znth r rest nil) 0).
    { intros r c Hr Hc.
      replace (Znth r rest nil) with (Znth (r + 1) (row :: rest) nil).
      2:{ rewrite Znth_cons by lia.
          replace (r + 1 - 1) with r by lia.
          reflexivity. }
      apply (Hnonneg (r + 1) c).
      * rewrite Zlength_correct in *. simpl in *. lia.
      * rewrite Znth_cons by lia.
        replace (r + 1 - 1) with r by lia.
        exact Hc. }
    rewrite (IH capacity
      (acc_nat + (count_water (nat_row_of_z row) + Z.to_nat capacity - 1) /
       Z.to_nat capacity)%nat
      (acc_z + row_trip_z row capacity)
      Hcap Hacc' Htail).
    reflexivity.
Qed.

Lemma required_trips_all_bridge : forall rows capacity,
  1 <= capacity ->
  (forall r c, 0 <= r < Zlength rows ->
    0 <= c < Zlength (Znth r rows nil) ->
    0 <= Znth c (Znth r rows nil) 0) ->
  Z.of_nat (required_trips_impl (nat_grid_of_z rows) (Z.to_nat capacity)) =
  trips_prefix_z rows (Zlength rows) capacity.
Proof.
  intros rows capacity Hcap Hnonneg.
  unfold required_trips_impl.
  unfold trips_prefix_z.
  replace (Z.to_nat (Zlength rows)) with (length rows)
    by (rewrite Zlength_correct; lia).
  rewrite firstn_all.
  apply required_trips_bridge_acc; try lia; try reflexivity.
  exact Hnonneg.
Qed.

Lemma problem_115_spec_z_of_trips_prefix : forall rows capacity ret,
  problem_115_pre_z rows capacity ->
  1 <= capacity ->
  ret = trips_prefix_z rows (Zlength rows) capacity ->
  (forall r c, 0 <= r < Zlength rows -> 0 <= c < Zlength (Znth r rows nil) -> 0 <= Znth c (Znth r rows nil) 0) ->
  problem_115_spec_z rows capacity ret.
Proof.
  intros rows capacity ret Hpre Hcap Hret Hnonneg.
  unfold problem_115_spec_z.
  unfold problem_115_spec.
  subst ret.
  pose proof (required_trips_all_bridge rows capacity Hcap Hnonneg) as Hbridge.
  apply Nat2Z.inj.
  rewrite Z2Nat.id.
  - symmetry. exact Hbridge.
  - rewrite <- Hbridge. lia.
Qed.

Local Close Scope bool_scope.

Ltac c115_default_rows :=
  repeat match goal with
  | Hlen : forall r : Z, _ -> Zlength (Znth r ?rs ?d) = ?m
    |- context[Zlength (Znth ?r ?rs ?d2)] =>
      rewrite (Znth_indep rs r d2 d) by lia
  | Hcell : forall r c : Z, _ -> 0 <= Znth c (Znth r ?rs ?d) 0 <= 1
    |- context[Znth ?c (Znth ?r ?rs nil) 0] =>
      rewrite (Znth_indep rs r nil d) by lia
  end.

Ltac c115_cell_bound :=
  match goal with
  | Hcell : forall r c : Z, _ -> _ |- context[Znth ?c (Znth ?r ?rs ?d) 0] =>
      pose proof (Hcell r c ltac:(repeat split; lia))
  end.

Ltac c115_quot_bound :=
  match goal with
  | |- context[Z.quot (?s - 1) ?cap] =>
      assert (0 <= Z.quot (s - 1) cap <= s - 1) by
        (split; [apply Z.quot_pos; lia | apply Z.quot_le_upper_bound; nia])
  end.

Ltac c115_basic :=
  pre_process_default; try entailer!;
  try c115_default_rows; try c115_cell_bound; try c115_quot_bound;
  try lia; try nia.



Lemma proof_of_max_fill_safety_wit_6 : max_fill_safety_wit_6.
Proof.
  c115_basic.
Qed.



Lemma proof_of_max_fill_safety_wit_8 : max_fill_safety_wit_8.
Proof.
  c115_basic.
Qed.



Lemma proof_of_max_fill_safety_wit_9 : max_fill_safety_wit_9.
Proof.
  c115_basic.
Qed.



Lemma proof_of_max_fill_entail_wit_1 : max_fill_entail_wit_1.
Proof.
  pre_process_default; try entailer!.
Qed.





Lemma proof_of_max_fill_entail_wit_2 : max_fill_entail_wit_2.
Proof.
  pre_process_default.
  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i
    grid_pre i grid_rows_pre rows).
  - dump_pre_spatial. lia.
  - Intros row_ptr.
    Exists row_ptr.
    rewrite row_sum_prefix_z_0.
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


Lemma proof_of_max_fill_entail_wit_3 : max_fill_entail_wit_3.
Proof.
  pre_process_default.
  Exists row_ptr_2.
  entailer!.
Qed.




Lemma proof_of_max_fill_entail_wit_4 : max_fill_entail_wit_4.
Proof.
  pre_process_default.
  rewrite (Znth_indep rows i nil __default__List_Z) by lia.
  rewrite (Znth_indep rows i nil __default__List_Z) in PreH17 by lia.
  pose proof (PreH15 i j ltac:(repeat split; lia)).
  assert (Hrow_len : Zlength (Znth i rows __default__List_Z) = grid_cols_pre)
    by (apply PreH14; lia).
  rewrite (row_sum_prefix_z_step (Znth i rows __default__List_Z) j)
    by (rewrite Hrow_len; lia).
  Exists row_ptr_2.
  entailer!.
Qed.




Lemma proof_of_max_fill_entail_wit_5 : max_fill_entail_wit_5.
Proof.
  pre_process_default.
  assert (j = grid_cols_pre) by lia; subst j.
  rewrite (Znth_indep rows i nil __default__List_Z) by lia.
  rewrite (Znth_indep rows i nil __default__List_Z) in PreH17 by lia.
  pose proof (IntPtrArray2.missing_i_merge_to_full
    grid_pre i grid_rows_pre row_ptr rows
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





Lemma proof_of_max_fill_entail_wit_6_1 : max_fill_entail_wit_6_1.
Proof.
  pre_process_default; try entailer!.
  - pose proof (trips_prefix_z_nonneg_bound_step
      i grid_cols_pre capacity_pre out sum ltac:(lia) ltac:(lia)
      ltac:(lia) ltac:(lia) ltac:(lia)) as Hbound.
    replace (Z.eqb sum 0) with false in Hbound
      by (symmetry; apply Z.eqb_neq; lia).
    destruct Hbound as [_ Hbound_hi]. exact Hbound_hi.
  - pose proof (trips_prefix_z_nonneg_bound_step
      i grid_cols_pre capacity_pre out sum ltac:(lia) ltac:(lia)
      ltac:(lia) ltac:(lia) ltac:(lia)) as Hbound.
    replace (Z.eqb sum 0) with false in Hbound
      by (symmetry; apply Z.eqb_neq; lia).
    destruct Hbound as [Hbound_lo _]. exact Hbound_lo.
  - assert (Hstep :
      trips_prefix_z rows (i + 1) capacity_pre =
      trips_prefix_z rows i capacity_pre +
      (if Z.eqb sum 0 then 0 else Z.quot (sum - 1) capacity_pre + 1)).
    { apply trips_prefix_z_step_from_sum with (n := grid_cols_pre); try lia. }
    rewrite Hstep.
    replace (Z.eqb sum 0) with false by (symmetry; apply Z.eqb_neq; lia).
    lia.
Qed.




Lemma proof_of_max_fill_entail_wit_6_2 : max_fill_entail_wit_6_2.
Proof.
  pre_process_default; try entailer!.
  assert (sum = 0) by lia; subst sum.
  assert (Hstep :
    trips_prefix_z rows (i + 1) capacity_pre =
    trips_prefix_z rows i capacity_pre +
    (if Z.eqb 0 0 then 0 else Z.quot (0 - 1) capacity_pre + 1)).
  { apply trips_prefix_z_step_from_sum with (n := grid_cols_pre); try lia. }
  rewrite Hstep.
  simpl.
  entailer!.
Qed.


Lemma proof_of_max_fill_return_wit_1 : max_fill_return_wit_1.
Proof.
  pre_process_default; try entailer!.
  apply problem_115_spec_z_of_trips_prefix; try lia.
  - exact PreH11.
  - rewrite PreH14.
    replace i with grid_rows_pre by lia.
    rewrite <- PreH10.
    reflexivity.
  - intros r c Hr Hc.
    assert (Hr_grid : 0 <= r < grid_rows_pre) by lia.
    assert (Hrow_eq : Znth r rows nil = Znth r rows __default__List_Z).
    { apply Znth_indep. lia. }
    assert (Hrow_len : Zlength (Znth r rows __default__List_Z) = grid_cols_pre).
    { apply PreH12. exact Hr_grid. }
    rewrite Hrow_eq in Hc.
    pose proof (PreH13 r c ltac:(repeat split; try lia)) as Hcell.
    rewrite Hrow_eq.
    tauto.
Qed.
