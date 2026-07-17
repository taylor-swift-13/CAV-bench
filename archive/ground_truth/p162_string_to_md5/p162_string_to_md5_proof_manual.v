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
From SimpleC.EE.CAV.ground_truth_p162_string_to_md5 Require Import p162_string_to_md5_goal.
From SimpleC.EE.CAV.ground_truth_p162_string_to_md5 Require Import p162_string_to_md5_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import p162_string_to_md5.
Local Open Scope sac.
Import ListNotations.

Lemma hex_digit_range_162 : forall n,
  0 <= n < 16 -> 48 <= md5_hex_digit_z n <= 102.
Proof.
  intros n Hn. unfold md5_hex_digit_z.
  destruct (Z.ltb n 10) eqn:E.
  - apply Z.ltb_lt in E. lia.
  - apply Z.ltb_ge in E. lia.
Qed.

Lemma hex_digit_signed_162 : forall n,
  0 <= n < 16 ->
  signed_last_nbits (md5_hex_digit_z n) 8 = md5_hex_digit_z n.
Proof.
  intros n Hn. apply signed_last_nbits_eq; [lia|].
  pose proof (hex_digit_range_162 n Hn). cbn. lia.
Qed.

Lemma firstn_succ_nth_162 : forall (n : nat) (xs : list Z),
  (n < length xs)%nat ->
  firstn (S n) xs = List.app (firstn n xs) [nth n xs 0].
Proof.
  induction n as [|n IH]; intros xs Hlt.
  - destruct xs; [simpl in Hlt; lia | reflexivity].
  - destruct xs as [|x xs]; [simpl in Hlt; lia |].
    simpl. f_equal. apply IH. simpl in Hlt. lia.
Qed.

Lemma firstn_step_162 : forall (xs : list Z) i,
  0 <= i < Zlength xs ->
  firstn (Z.to_nat (i + 1)) xs =
  List.app (firstn (Z.to_nat i) xs) [Znth i xs 0].
Proof.
  intros xs i Hi.
  assert (Hnat : Z.to_nat (i + 1) = S (Z.to_nat i)).
  { rewrite Z2Nat.inj_add by lia.
    change (Z.to_nat i + 1 = S (Z.to_nat i))%nat. lia. }
  rewrite Hnat.
  rewrite firstn_succ_nth_162.
  - unfold Znth. reflexivity.
  - apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct. lia.
Qed.

Lemma hex_prefix_step_162 : forall digest i output,
  0 <= i < Zlength digest ->
  md5_hex_prefix_z digest i output ->
  md5_hex_prefix_z digest (i + 1)
    (List.app output (md5_byte_hex_z (Znth i digest 0))).
Proof.
  intros digest i output Hi Hprefix.
  unfold md5_hex_prefix_z in *.
  rewrite firstn_step_162 by exact Hi.
  rewrite map_app, concat_app. simpl.
  rewrite Hprefix. reflexivity.
Qed.

Lemma hex_prefix_final_162 : forall input output i,
  i = 16 -> Zlength (md5_digest_z input) = 16 ->
  md5_hex_prefix_z (md5_digest_z input) i output ->
  output = md5_hex_z input.
Proof.
  intros input output i Hi Hlen Hprefix. subst i.
  unfold md5_hex_prefix_z in Hprefix.
  unfold md5_hex_z.
  assert (Hnat : Z.to_nat 16 = length (md5_digest_z input)).
  { change (16%nat = length (md5_digest_z input)).
    apply Nat2Z.inj. rewrite <- Zlength_correct. exact Hlen. }
  rewrite Hnat, firstn_all in Hprefix. exact Hprefix.
Qed.

Lemma md5_byte_hex_z_length_162 : forall b,
  length (md5_byte_hex_z b) = 2%nat.
Proof.
  intros b. unfold md5_byte_hex_z. reflexivity.
Qed.

Lemma md5_hex_concat_length_162 : forall digest,
  length (concat (map md5_byte_hex_z digest)) = (2 * length digest)%nat.
Proof.
  induction digest as [|b bs IH]; [reflexivity|].
  cbn [map concat].
  rewrite length_app, md5_byte_hex_z_length_162, IH. simpl. nia.
Qed.

Lemma md5_hex_z_length_162 : forall input,
  Zlength (md5_digest_z input) = 16 ->
  Zlength (md5_hex_z input) = 32.
Proof.
  intros input Hlen.
  unfold md5_hex_z.
  rewrite Zlength_correct, md5_hex_concat_length_162.
  rewrite Zlength_correct in Hlen. lia.
Qed.

Lemma proof_of_md5_hex_digit_c_return_wit_1 : md5_hex_digit_c_return_wit_1.
Proof.
  unfold md5_hex_digit_c_return_wit_1. left.
  intros. Intros. entailer!.
  unfold md5_hex_digit_z. destruct ((n_pre <? 10)%Z) eqn:Hcmp.
  - apply Z.ltb_lt in Hcmp. lia.
  - lia.
Qed.

Lemma proof_of_md5_hex_digit_c_return_wit_2 : md5_hex_digit_c_return_wit_2.
Proof.
  unfold md5_hex_digit_c_return_wit_2. left.
  intros. Intros. entailer!.
  unfold md5_hex_digit_z. destruct ((n_pre <? 10)%Z) eqn:Hcmp.
  - lia.
  - apply Z.ltb_ge in Hcmp. lia.
Qed.

Lemma proof_of_string_to_md5_entail_wit_1 : string_to_md5_entail_wit_1.
Proof.
  unfold string_to_md5_entail_wit_1. left.
  intros. Intros.
  destruct PreH2 as [Hlen Hbounds].
  assert (Hbounds_goal : forall k, 0 <= k < 16 ->
    ((((0 <= Znth k (md5_digest_z input_s) 0 < 256 /\
       0 <= Znth k (md5_digest_z input_s) 0 / 16) /\
       Znth k (md5_digest_z input_s) 0 / 16 < 16) /\
       0 <= Znth k (md5_digest_z input_s) 0 mod 16) /\
       Znth k (md5_digest_z input_s) 0 mod 16 < 16)).
  { intros k Hk. specialize (Hbounds k Hk). cbn zeta in Hbounds.
    exact Hbounds. }
  Exists (@nil Z).
  unfold md5_hex_prefix_z, store_string. entailer!.
  rewrite CharArray.seg_empty.
  sep_apply_l_atomic (CharArray.undef_full_to_undef_seg retval_2 33).
  cancel. entailer!.
  Unshelve.
  intros k Hk. specialize (Hbounds_goal k Hk).
  rewrite Z.quot_div_nonneg by lia.
  rewrite Z.rem_mod_nonneg by lia.
  exact Hbounds_goal.
  destruct input_s as [|x xs].
  - simpl in PreH5. contradiction.
  - unfold string_length. rewrite Zlength_cons.
    pose proof (Zlength_nonneg xs). lia.
Qed.

Lemma proof_of_string_to_md5_entail_wit_2 : string_to_md5_entail_wit_2.
Proof.
  unfold string_to_md5_entail_wit_2. left.
  intros. Intros.
  pose proof (PreH9 i ltac:(lia)) as Hbyte.
  cbn zeta in Hbyte.
  destruct Hbyte as [[[[[Hb0 Hb256] Hq0] Hq16] Hr0] Hr16].
  assert (Hqeq : (Znth i (md5_digest_z input_s) 0 ÷ 16) =
      Znth i (md5_digest_z input_s) 0 / 16).
  { apply Z.quot_div_nonneg; lia. }
  assert (Hreq : (Znth i (md5_digest_z input_s) 0 % 16) =
      Znth i (md5_digest_z input_s) 0 mod 16).
  { apply Z.rem_mod_nonneg; lia. }
  rewrite Hqeq in PreH2. rewrite Hreq in PreH1.
  assert (Hhi : 0 <= Znth i (md5_digest_z input_s) 0 / 16 < 16) by lia.
  assert (Hlo : 0 <= Znth i (md5_digest_z input_s) 0 mod 16 < 16) by lia.
  assert (Hshi : signed_last_nbits retval 8 = retval).
  { rewrite PreH2. apply hex_digit_signed_162. exact Hhi. }
  assert (Hslo : signed_last_nbits retval_2 8 = retval_2).
  { rewrite PreH1. apply hex_digit_signed_162. exact Hlo. }
  rewrite Hshi, Hslo, PreH2, PreH1.
  Exists (List.app output_2
    (md5_byte_hex_z (Znth i (md5_digest_z input_s) 0))).
  assert (Hprefix : md5_hex_prefix_z (md5_digest_z input_s) (i + 1)
      (List.app output_2
        (md5_byte_hex_z (Znth i (md5_digest_z input_s) 0)))).
  { apply hex_prefix_step_162; [lia|exact PreH11]. }
  unfold md5_byte_hex_z.
  entailer!.
  - unfold store_string. cancel.
    replace (2 * (i + 1)) with (2 * i + 1 + 1) by lia.
    assert (Happ :
      (output_2 +:: md5_hex_digit_z (Znth i (md5_digest_z input_s) 0 / 16))
        +:: md5_hex_digit_z (Znth i (md5_digest_z input_s) 0 mod 16) =
      output_2 ++
        [md5_hex_digit_z (Znth i (md5_digest_z input_s) 0 / 16);
         md5_hex_digit_z (Znth i (md5_digest_z input_s) 0 mod 16)]).
    { rewrite <- app_assoc. reflexivity. }
    rewrite Happ. entailer!.
  - rewrite Zlength_app, PreH10, Zlength_cons, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_string_to_md5_return_wit_2 : string_to_md5_return_wit_2.
Proof.
  unfold string_to_md5_return_wit_2.
  intros.
  assert (Hi : i = 16) by lia.
  assert (Houtput : output = md5_hex_z input_s).
  { apply hex_prefix_final_162 with (i := i); assumption. }
  assert (Hnonempty : input_s <> nil).
  { intro E. subst input_s. unfold string_length in PreH5.
    rewrite Zlength_nil in PreH5. lia. }
  Right. Exists text. Exists output.
  unfold problem_162_spec_z.
  destruct input_s as [|x xs]; [contradiction|].
  simpl in Houtput. rewrite Houtput.
  rewrite Hi in *.
  rewrite Houtput in *.
  assert (Hhexlen : Zlength (md5_hex_z (x :: xs)) = 32).
  { apply md5_hex_z_length_162. exact PreH6. }
  rewrite CharArray.undef_seg_empty by lia.
  sep_apply_l_atomic (CharArray.seg_to_full out_str 0 33
    (List.app (md5_hex_z (x :: xs)) [0])).
  replace (out_str + 0 * sizeof(CHAR)) with out_str by lia.
  replace (33 - 0) with 33 by lia.
  entailer!.
  Unshelve. unfold store_string. rewrite Hhexlen. entailer!.
Qed.

Lemma proof_of_string_to_md5_return_wit_1 : string_to_md5_return_wit_1.
Proof.
  unfold string_to_md5_return_wit_1. left.
  intros. Intros.
  assert (Hnil : input_s = nil).
  { destruct input_s as [|x xs]; [reflexivity|].
    unfold problem_162_pre_z in PreH6.
    inversion PreH6 as [|a l Ha Hall]; subst. destruct Ha as [Hx Hxmax].
    rewrite c_string_Znth_inside in PreH3.
    2: { unfold string_length. rewrite Zlength_cons.
         pose proof (Zlength_nonneg xs). lia. }
    rewrite Znth0_cons in PreH3. lia. }
  subst input_s.
  Exists text_pre. Exists [78;111;110;101].
  unfold problem_162_spec_z. simpl.
  rewrite CharArray.undef_seg_empty by lia.
  unfold CharArray.full, store_array, store_string, c_string, string_length.
  simpl. entailer!.
  Unshelve. unfold CharArray.full, store_array. simpl. entailer!.
Qed.

Lemma proof_of_string_to_md5_partial_solve_wit_5_pure :
  string_to_md5_partial_solve_wit_5_pure.
Proof.
  unfold string_to_md5_partial_solve_wit_5_pure. left.
  intros. Intros.
  specialize (PreH7 i ltac:(lia)).
  cbn zeta in PreH7. entailer!.
Qed.

Lemma proof_of_string_to_md5_partial_solve_wit_7_pure :
  string_to_md5_partial_solve_wit_7_pure.
Proof.
  unfold string_to_md5_partial_solve_wit_7_pure. left.
  intros. Intros.
  specialize (PreH8 i ltac:(lia)).
  cbn zeta in PreH8. entailer!.
Qed.
