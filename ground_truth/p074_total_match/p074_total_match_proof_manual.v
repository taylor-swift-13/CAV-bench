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
