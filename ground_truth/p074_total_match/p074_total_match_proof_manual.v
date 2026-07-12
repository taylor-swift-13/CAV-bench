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
From SimpleC.EE.CAV.ground_truth_p074_total_match Require Import p074_total_match_goal.
From SimpleC.EE.CAV.ground_truth_p074_total_match Require Import p074_total_match_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import p074_total_match.
Local Open Scope sac.

(* BEGIN migrated companion-spec proofs *)
Module MigratedCompanionProofs.
Local Open Scope bool_scope.
Import ListNotations.
Open Scope string_scope.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.



Lemma String_length_string_of_list_z_74 : forall l,
  String.length (string_of_list_z_74 l) = List.length l.
Proof.
  induction l as [| x xs IH]; simpl; congruence.
Qed.

Lemma row_string_length_z_74 : forall row,
  Z.of_nat (String.length (row_string_z_74 row)) = row_len_z_74 row.
Proof.
  intros row.
  unfold row_string_z_74, row_len_z_74, string_length.
  rewrite String_length_string_of_list_z_74.
  rewrite Zlength_correct.
  reflexivity.
Qed.

Lemma rows_well_formed_74_row : forall rows n k,
  rows_well_formed_74 rows n ->
  0 <= k < n ->
  let row := Znth k rows nil in
  let payload := row_payload_z_74 row in
  row = c_string payload /\
  valid_string payload /\
  string_length payload < INT_MAX /\
  Zlength row = string_length payload + 1.
Proof.
  intros rows n k [Hlen [_ [_ Hwf]]] Hk row payload.
  specialize (Hwf k Hk).
  destruct Hwf as [Hrow [Hvalid Hlt]].
  split; [exact Hrow|].
  split; [exact Hvalid|].
  split; [exact Hlt|].
  subst row payload.
  change (Zlength (Znth k rows nil) =
          Zlength (row_payload_z_74 (Znth k rows nil)) + 1).
  rewrite Hrow at 1.
  unfold c_string.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma total_prefix_state_74_initial : forall rows,
  total_prefix_state_74 rows 0 0.
Proof.
  intros rows.
  unfold total_prefix_state_74, total_prefix_len_z_74.
  split; [rewrite Zlength_correct; lia|].
  reflexivity.
Qed.

Lemma firstn_succ_Z_74 : forall (rows : list (list Z)) k,
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

Lemma rows_total_len_z_74_app : forall a b,
  rows_total_len_z_74 (a ++ b) =
  rows_total_len_z_74 a + rows_total_len_z_74 b.
Proof.
  induction a as [| row rest IH]; intros b; simpl.
  - lia.
  - rewrite IH. lia.
Qed.

Lemma total_prefix_state_74_step : forall rows k total len,
  total_prefix_state_74 rows k total ->
  0 <= k < Zlength rows ->
  len = row_len_z_74 (Znth k rows nil) ->
  total_prefix_state_74 rows (k + 1) (total + len).
Proof.
  intros rows k total len [Hkbounds Htotal] Hk Hlen.
  split; [lia|].
  unfold total_prefix_len_z_74 in *.
  rewrite firstn_succ_Z_74 by exact Hk.
  rewrite rows_total_len_z_74_app.
  simpl.
  lia.
Qed.

Lemma total_prefix_state_74_full : forall rows n total,
  Zlength rows = n ->
  total_prefix_state_74 rows n total ->
  total = rows_total_len_z_74 rows.
Proof.
  intros rows n total Hlen [_ Htotal].
  unfold total_prefix_len_z_74 in Htotal.
  subst total.
  rewrite firstn_all2; [reflexivity|].
  rewrite Zlength_correct in Hlen.
  lia.
Qed.

Lemma row_len_z_74_nonneg : forall row,
  0 <= row_len_z_74 row.
Proof.
  intros row.
  unfold row_len_z_74, string_length.
  apply Zlength_nonneg.
Qed.

Lemma rows_total_len_z_74_nonneg : forall rows,
  0 <= rows_total_len_z_74 rows.
Proof.
  induction rows as [| row rest IH]; simpl; [lia|].
  pose proof (row_len_z_74_nonneg row).
  lia.
Qed.

Lemma total_prefix_state_74_bound : forall rows k total,
  total_prefix_state_74 rows k total ->
  total <= rows_total_len_z_74 rows.
Proof.
  intros rows k total [_ Htotal].
  unfold total_prefix_len_z_74 in Htotal.
  subst total.
  rewrite <- (firstn_skipn (Z.to_nat k) rows) at 2.
  rewrite rows_total_len_z_74_app.
  pose proof (rows_total_len_z_74_nonneg (skipn (Z.to_nat k) rows)).
  lia.
Qed.

Lemma total_prefix_state_74_nonneg : forall rows k total,
  total_prefix_state_74 rows k total ->
  0 <= total.
Proof.
  intros rows k total [_ Htotal].
  unfold total_prefix_len_z_74 in Htotal.
  subst total.
  apply rows_total_len_z_74_nonneg.
Qed.

Lemma fold_left_nat_add_start_74 : forall l x,
  fold_left Nat.add l x = (x + fold_left Nat.add l 0)%nat.
Proof.
  induction l as [| a rest IH]; intros x; simpl; [lia|].
  rewrite IH.
  rewrite (IH a).
  lia.
Qed.

Lemma fold_left_string_length_start_74 : forall l x,
  fold_left
    (fun (acc : nat) (s : string) => (acc + String.length s)%nat)
    l x =
  (x +
   fold_left
     (fun (acc : nat) (s : string) => (acc + String.length s)%nat)
     l 0)%nat.
Proof.
  induction l as [| a rest IH]; intros x; simpl; [lia|].
  rewrite IH.
  rewrite (IH (String.length a)).
  lia.
Qed.

Lemma rows_total_len_z_74_nat_sum : forall rows,
  Z.of_nat
    (fold_left
       (fun (acc : nat) (s : string) => (acc + String.length s)%nat)
       (rows_to_strings_z_74 rows) 0%nat) =
  rows_total_len_z_74 rows.
Proof.
  induction rows as [| row rest IH]; simpl.
  - reflexivity.
  - rewrite fold_left_string_length_start_74.
    rewrite Nat2Z.inj_add.
    rewrite IH.
    rewrite row_string_length_z_74.
    lia.
Qed.

Lemma problem_74_spec_z_rows1 : forall rows1 rows2,
  rows_total_len_z_74 rows1 <= rows_total_len_z_74 rows2 ->
  problem_74_spec_z rows1 rows2 rows1.
Proof.
  intros rows1 rows2 Hle.
  unfold problem_74_spec_z, problem_74_spec.
  left.
  split; [| reflexivity].
  apply Nat2Z.inj_le.
  repeat rewrite rows_total_len_z_74_nat_sum.
  exact Hle.
Qed.

Lemma problem_74_spec_z_rows2 : forall rows1 rows2,
  rows_total_len_z_74 rows1 > rows_total_len_z_74 rows2 ->
  problem_74_spec_z rows1 rows2 rows2.
Proof.
  intros rows1 rows2 Hgt.
  unfold problem_74_spec_z, problem_74_spec.
  right.
  split; [| reflexivity].
  apply Nat2Z.inj_lt.
  repeat rewrite rows_total_len_z_74_nat_sum.
  lia.
Qed.
End MigratedCompanionProofs.
Export MigratedCompanionProofs.
(* END migrated companion-spec proofs *)

Ltac c74_row_facts Hwf rows n idx :=
  let Hrowfacts := fresh "Hrowfacts" in
  pose proof (rows_well_formed_74_row rows n idx Hwf ltac:(lia)) as Hrowfacts;
  simpl in Hrowfacts;
  destruct Hrowfacts as [? [? [? ?]]].

Ltac c74_merge_row arr n idx row_ptr rows :=
  let Hmerge := fresh "Hmerge" in
  pose proof (CharPtrArray2.missing_i_merge_to_full
    arr idx n row_ptr rows (Znth idx rows nil)) as Hmerge;
  unfold StorePtrAsElement.storeA in Hmerge;
  try rewrite sizeof_ptr in Hmerge;
  try rewrite sizeof_ptr;
  change (CharPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth idx rows nil)) (Znth idx rows nil))
    with (CharArray.full row_ptr
      (Zlength (Znth idx rows nil)) (Znth idx rows nil)) in Hmerge;
  sep_apply Hmerge; try lia;
  rewrite replace_Znth_Znth by lia.

Lemma proof_of_total_match_safety_wit_6 : total_match_safety_wit_6.
Proof.
  constructor; pre_process_default; entailer!.
  all:
    assert (Hlen_eq : retval = row_len_z_74 (Znth i rows1 nil))
      by (subst retval; unfold row_len_z_74; reflexivity);
    assert (Hi_rows : 0 <= i < Zlength rows1)
      by (destruct PreH8 as [Hrows_len _]; lia);
    pose proof (total_prefix_state_74_step rows1 i num1 retval PreH11 Hi_rows Hlen_eq) as Hstep;
    pose proof (total_prefix_state_74_bound rows1 (i + 1) (num1 + retval) Hstep);
    pose proof (total_prefix_state_74_nonneg rows1 (i + 1) (num1 + retval) Hstep);
    lia.
Qed.

Lemma proof_of_total_match_safety_wit_9 : total_match_safety_wit_9.
Proof.
  constructor; pre_process_default; entailer!.
  all:
    assert (Hlen_eq : retval = row_len_z_74 (Znth i rows2 nil))
      by (subst retval; unfold row_len_z_74; reflexivity);
    assert (Hi_rows : 0 <= i < Zlength rows2)
      by (destruct PreH9 as [Hrows_len _]; lia);
    pose proof (total_prefix_state_74_step rows2 i num2 retval PreH11 Hi_rows Hlen_eq) as Hstep;
    pose proof (total_prefix_state_74_bound rows2 (i + 1) (num2 + retval) Hstep);
    pose proof (total_prefix_state_74_nonneg rows2 (i + 1) (num2 + retval) Hstep);
    lia.
Qed.

Lemma proof_of_total_match_entail_wit_1 : total_match_entail_wit_1.
Proof.
  constructor.
  - pre_process_default; entailer!.
    all: try solve [destruct PreH5 as [_ [_ [Hbounds _]]]; lia].
    all: try solve [destruct PreH6 as [_ [_ [Hbounds _]]]; lia].
    apply total_prefix_state_74_initial.
Qed.

Lemma proof_of_total_match_entail_wit_2 : total_match_entail_wit_2.
Proof.
  constructor.
  - pre_process_default.
    c74_row_facts PreH7 rows1 lst1_size_pre i.
    sep_apply_l_atomic (CharPtrArray2.full_split_to_missing_i lst1_pre i lst1_size_pre rows1).
    + dump_pre_spatial; lia.
    + Intros row_ptr.
      Exists row_ptr.
      unfold StorePtrAsElement.storeA.
      rewrite sizeof_ptr.
      change (CharPtrArray2.ElemArray.full row_ptr
        (Zlength (Znth i rows1 nil)) (Znth i rows1 nil))
        with (CharArray.full row_ptr (Zlength (Znth i rows1 nil)) (Znth i rows1 nil)).
      unfold store_string.
      rewrite <- H2.
      rewrite <- H.
      entailer!.
Qed.

Lemma proof_of_total_match_entail_wit_3 : total_match_entail_wit_3.
Proof.
  constructor.
  - pre_process_default; try entailer!; try lia.
    c74_row_facts PreH8 rows1 lst1_size_pre i.
    unfold store_string.
    rewrite <- H2.
    rewrite <- H.
    c74_merge_row lst1_pre lst1_size_pre i row_ptr rows1.
    entailer!.
    + assert (Hi_rows : 0 <= i < Zlength rows1)
        by (destruct PreH8 as [Hrows_len _]; lia).
      assert (Hlen_eq : retval = row_len_z_74 (Znth i rows1 nil))
        by (subst retval; unfold row_len_z_74; reflexivity).
      eapply total_prefix_state_74_step; eauto.
    + subst retval. apply string_length_nonneg.
Qed.

Lemma proof_of_total_match_entail_wit_5 : total_match_entail_wit_5.
Proof.
  constructor.
  - pre_process_default; entailer!.
    + subst num2. apply total_prefix_state_74_initial.
    + replace i with lst1_size_pre in PreH10 by lia.
      destruct PreH7 as [Hlen_rows _].
      eapply total_prefix_state_74_full with (n := lst1_size_pre); eauto.
    + destruct PreH8 as [Hrows2_len _].
      pose proof (Zlength_nonneg rows2). lia.
Qed.

Lemma proof_of_total_match_entail_wit_6 : total_match_entail_wit_6.
Proof.
  constructor.
  - pre_process_default.
    c74_row_facts PreH8 rows2 lst2_size_pre i.
    sep_apply_l_atomic (CharPtrArray2.full_split_to_missing_i lst2_pre i lst2_size_pre rows2).
    + dump_pre_spatial; lia.
    + Intros row_ptr.
      Exists row_ptr.
      unfold StorePtrAsElement.storeA.
      rewrite sizeof_ptr.
      change (CharPtrArray2.ElemArray.full row_ptr
        (Zlength (Znth i rows2 nil)) (Znth i rows2 nil))
        with (CharArray.full row_ptr (Zlength (Znth i rows2 nil)) (Znth i rows2 nil)).
      unfold store_string.
      rewrite <- H2.
      rewrite <- H.
      entailer!.
Qed.

Lemma proof_of_total_match_entail_wit_7 : total_match_entail_wit_7.
Proof.
  constructor.
  - pre_process_default; try entailer!; try lia.
    c74_row_facts PreH9 rows2 lst2_size_pre i.
    unfold store_string.
    rewrite <- H2.
    rewrite <- H.
    c74_merge_row lst2_pre lst2_size_pre i row_ptr rows2.
    entailer!.
    + assert (Hi_rows : 0 <= i < Zlength rows2)
        by (destruct PreH9 as [Hrows_len _]; lia).
      assert (Hlen_eq : retval = row_len_z_74 (Znth i rows2 nil))
        by (subst retval; unfold row_len_z_74; reflexivity).
      eapply total_prefix_state_74_step; eauto.
    + subst retval. apply string_length_nonneg.
Qed.

Lemma proof_of_total_match_return_wit_1 : total_match_return_wit_1.
Proof.
  pre_process_default.
  eapply derivable1_trans with
    (y := EX data : Z, EX output_rows : list (list Z), EX output_size : Z,
      “ retval <> 0 ” &&
      “ 0 <= output_size ” &&
      “ output_size <= 100 ” &&
      “ problem_74_spec_z rows1 rows2 output_rows ” &&
      “ data = lst1_pre ” &&
      “ output_size = lst1_size_pre ” &&
      “ output_rows = rows1 ” &&
      ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data) **
      ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size) **
      CharPtrArray2.full lst1_pre lst1_size_pre rows1 **
      CharPtrArray2.full lst2_pre lst2_size_pre rows2).
  - Exists lst1_pre rows1 lst1_size_pre.
    entailer!.
    + replace i with lst2_size_pre in PreH12 by lia.
      assert (Hnum2 : num2 = rows_total_len_z_74 rows2).
      {
        destruct PreH10 as [Hlen_rows _].
        eapply total_prefix_state_74_full with (n := lst2_size_pre); eauto.
      }
      subst num1 num2.
      apply problem_74_spec_z_rows1. lia.
    + destruct PreH9 as [_ [Hsize_bounds _]]. lia.
    + destruct PreH9 as [_ [Hsize_bounds _]]. lia.
  - apply derivable1_orp_intros1.
Qed.

Lemma proof_of_total_match_return_wit_2 : total_match_return_wit_2.
Proof.
  pre_process_default.
  eapply derivable1_trans with
    (y := EX data : Z, EX output_rows : list (list Z), EX output_size : Z,
      “ retval <> 0 ” &&
      “ 0 <= output_size ” &&
      “ output_size <= 100 ” &&
      “ problem_74_spec_z rows1 rows2 output_rows ” &&
      “ data = lst2_pre ” &&
      “ output_size = lst2_size_pre ” &&
      “ output_rows = rows2 ” &&
      ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data) **
      ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size) **
      CharPtrArray2.full lst1_pre lst1_size_pre rows1 **
      CharPtrArray2.full lst2_pre lst2_size_pre rows2).
  - Exists lst2_pre rows2 lst2_size_pre.
    entailer!.
    + replace i with lst2_size_pre in PreH12 by lia.
      assert (Hnum2 : num2 = rows_total_len_z_74 rows2).
      {
        destruct PreH10 as [Hlen_rows _].
        eapply total_prefix_state_74_full with (n := lst2_size_pre); eauto.
      }
      subst num1 num2.
      apply problem_74_spec_z_rows2. lia.
    + destruct PreH10 as [_ [Hsize_bounds _]]. lia.
  - apply derivable1_orp_intros2.
Qed.
