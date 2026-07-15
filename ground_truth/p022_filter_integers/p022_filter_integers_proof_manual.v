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
From SimpleC.EE.CAV.ground_truth_p022_filter_integers Require Import p022_filter_integers_goal.
From SimpleC.EE.CAV.ground_truth_p022_filter_integers Require Import p022_filter_integers_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p022_filter_integers.
Local Open Scope sac.

Import ListNotations.

Lemma filter_integer_payloads_firstn_succ :
  forall n tags values,
    List.length tags = List.length values ->
    (n < List.length tags)%nat ->
    filter_integer_payloads (firstn (S n) tags) (firstn (S n) values) =
      filter_integer_payloads (firstn n tags) (firstn n values) ++
      if Z.eqb (nth n tags 0) 0 then [nth n values 0] else [].
Proof.
  induction n as [| n IH].
  - intros tags values Hlen Hlt.
    destruct tags as [| tag tags]; [simpl in Hlt; lia|].
    destruct values as [| value values]; [simpl in Hlen; discriminate|].
    simpl. destruct (Z.eqb tag 0); reflexivity.
  - intros tags values Hlen Hlt.
    destruct tags as [| tag tags]; [simpl in Hlt; lia|].
    destruct values as [| value values]; [simpl in Hlen; discriminate|].
    simpl in Hlen, Hlt |- *.
    injection Hlen as Hlen.
    change
      ((if Z.eqb tag 0
        then value :: filter_integer_payloads (firstn (S n) tags)
                                              (firstn (S n) values)
        else filter_integer_payloads (firstn (S n) tags)
                                     (firstn (S n) values)) =
       (if Z.eqb tag 0
        then value :: filter_integer_payloads (firstn n tags) (firstn n values)
        else filter_integer_payloads (firstn n tags) (firstn n values)) ++
       (if Z.eqb (nth n tags 0) 0 then [nth n values 0] else [])).
    rewrite (IH tags values Hlen) by lia.
    destruct (Z.eqb tag 0); simpl; reflexivity.
Qed.

Lemma filter_integer_payloads_step_int :
  forall tags values i,
    0 <= i -> i < Zlength tags ->
    Zlength tags = Zlength values -> Znth i tags 0 = 0 ->
    filter_integer_payloads (firstn (Z.to_nat (i + 1)) tags)
                            (firstn (Z.to_nat (i + 1)) values) =
    filter_integer_payloads (firstn (Z.to_nat i) tags)
                            (firstn (Z.to_nat i) values) ++ [Znth i values 0].
Proof.
  intros tags values i Hi Hilt Hlen Htag.
  assert (Hsucc : Z.to_nat (i + 1) = S (Z.to_nat i)).
  { rewrite Z2Nat.inj_add by lia. simpl. lia. }
  assert (Hlen_nat : List.length tags = List.length values).
  { apply Nat2Z.inj. rewrite <- !Zlength_correct. exact Hlen. }
  assert (Hi_nat : (Z.to_nat i < List.length tags)%nat).
  { apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct. exact Hilt. }
  rewrite Hsucc, filter_integer_payloads_firstn_succ by assumption.
  unfold Znth in Htag |- *.
  rewrite Htag. reflexivity.
Qed.

Lemma filter_integer_payloads_step_nonint :
  forall tags values i,
    0 <= i -> i < Zlength tags ->
    Zlength tags = Zlength values -> Znth i tags 0 <> 0 ->
    filter_integer_payloads (firstn (Z.to_nat (i + 1)) tags)
                            (firstn (Z.to_nat (i + 1)) values) =
    filter_integer_payloads (firstn (Z.to_nat i) tags)
                            (firstn (Z.to_nat i) values).
Proof.
  intros tags values i Hi Hilt Hlen Htag.
  assert (Hsucc : Z.to_nat (i + 1) = S (Z.to_nat i)).
  { rewrite Z2Nat.inj_add by lia. simpl. lia. }
  assert (Hlen_nat : List.length tags = List.length values).
  { apply Nat2Z.inj. rewrite <- !Zlength_correct. exact Hlen. }
  assert (Hi_nat : (Z.to_nat i < List.length tags)%nat).
  { apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct. exact Hilt. }
  rewrite Hsucc, filter_integer_payloads_firstn_succ by assumption.
  unfold Znth in Htag.
  apply Z.eqb_neq in Htag. rewrite Htag. apply app_nil_r.
Qed.

Lemma proof_of_filter_integers_entail_wit_1 : filter_integers_entail_wit_1.
Proof.
  unfold filter_integers_entail_wit_1.
  left. intros. Intros. Exists (@nil Z).
  entailer!.
  rewrite IntArray.seg_empty.
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg retval_2 values_size_pre).
  cancel. entailer!.
Qed.

Lemma proof_of_filter_integers_entail_wit_2_1 : filter_integers_entail_wit_2_1.
Proof.
  unfold filter_integers_entail_wit_2_1.
  left. intros. Intros.
  Exists (output_2 ++ [Znth i values 0]). entailer!.
  - unfold problem_22_prefix_c in *.
    subst output_2.
    symmetry. apply filter_integer_payloads_step_int; try lia.
  - rewrite Zlength_app, PreH12, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_filter_integers_entail_wit_2_2 : filter_integers_entail_wit_2_2.
Proof.
  unfold filter_integers_entail_wit_2_2.
  left. intros. Intros. Exists output_2. entailer!.
  unfold problem_22_prefix_c in *.
  subst output_2.
  symmetry. apply filter_integer_payloads_step_nonint; try lia.
Qed.

Lemma proof_of_filter_integers_return_wit_1 : filter_integers_return_wit_1.
Proof.
  unfold filter_integers_return_wit_1.
  intros. Right. Intros.
  Exists output_2 output_size data_2. entailer!.
  unfold problem_22_spec_c, problem_22_prefix_c in *.
  assert (Hi : i = values_size_pre) by lia. subst i.
  assert (Htags : Z.to_nat values_size_pre = List.length tags).
  { apply Nat2Z.inj. rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct. lia. }
  assert (Hvalues : Z.to_nat values_size_pre = List.length values).
  { apply Nat2Z.inj. rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct. lia. }
  assert (Hlengths : List.length tags = List.length values) by lia.
  rewrite Htags in PreH13.
  rewrite firstn_all, Hlengths, firstn_all in PreH13.
  exact PreH13.
Qed.
