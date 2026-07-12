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
From SimpleC.EE.CAV.ground_truth_p148_bf Require Import p148_bf_goal.
From SimpleC.EE.CAV.ground_truth_p148_bf Require Import p148_bf_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import p148_bf.
Local Open Scope sac.

(* BEGIN migrated companion-spec proofs *)
Module MigratedCompanionProofs.
Local Open Scope bool_scope.
Import ListNotations.
Local Open Scope string_scope.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Import naive_C_Rules.
Local Open Scope sac.



Lemma Znth_In_range_148 : forall (l : list Z) i d,
  0 <= i < Zlength l ->
  In (Znth i l d) l.
Proof.
  intros l i d Hi.
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hi.
  lia.
Qed.

Ltac destruct_planet_index_148 n Hn :=
  let Hcases := fresh "Hcases" in
  assert (n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/
          n = 4 \/ n = 5 \/ n = 6 \/ n = 7) as Hcases by lia;
  repeat (destruct Hcases as [Hcases | Hcases];
          [subst n |]);
  [ idtac | idtac | idtac | idtac | idtac | idtac | idtac | subst n ].

Lemma planet_payload_ascii_148 : forall n c,
  0 <= n <= 7 ->
  In c (planet_payload_148 n) ->
  0 <= c <= 127.
Proof.
  intros n c Hn Hin.
  destruct_planet_index_148 n Hn;
    vm_compute in Hin;
    repeat (destruct Hin as [Hin | Hin]; [subst; lia |]);
    contradiction.
Qed.

Lemma planet_payload_nonzero_148 : forall n c,
  0 <= n <= 7 ->
  In c (planet_payload_148 n) ->
  c <> 0.
Proof.
  intros n c Hn Hin.
  destruct_planet_index_148 n Hn;
    vm_compute in Hin;
    repeat (destruct Hin as [Hin | Hin]; [subst; lia |]);
    contradiction.
Qed.

Lemma planet_payload_valid_string_148 : forall n,
  0 <= n <= 7 ->
  string_lib.valid_string (planet_payload_148 n).
Proof.
  intros n Hn.
  unfold string_lib.valid_string, string_lib.all_ascii, string_lib.no_inner_nul.
  split; intros i Hi;
    pose proof (Znth_In_range_148 (planet_payload_148 n) i 0 Hi) as Hin.
  - apply planet_payload_ascii_148 with (n := n); assumption.
  - apply planet_payload_nonzero_148 with (n := n); assumption.
Qed.

Lemma planet_payload_length_bound_148 : forall n,
  0 <= n <= 7 ->
  string_lib.string_length (planet_payload_148 n) < INT_MAX.
Proof.
  intros n Hn.
  destruct_planet_index_148 n Hn;
    unfold string_lib.string_length, planet_payload_148, lit_payload_148,
      planet_literal_148;
    unfold mercury_literal_148, venus_literal_148, earth_literal_148,
      mars_literal_148, jupiter_literal_148, saturn_literal_148,
      uranus_literal_148, neptune_literal_148;
    rewrite StringToList_length;
    unfold StringLength; simpl; lia.
Qed.

Lemma planet_payloads_string_safe_148_proof :
  planet_payloads_string_safe_148.
Proof.
  unfold planet_payloads_string_safe_148.
  repeat split;
    try solve
      [ apply planet_payload_valid_string_148; lia
      | apply planet_payload_length_bound_148; lia ].
Qed.

Lemma ascii_nat_to_z_148 : forall c,
  Z.of_nat (nat_of_ascii c) = AsciiToZ c.
Proof.
  intros c.
  unfold AsciiToZ, nat_of_ascii.
  rewrite N_nat_Z.
  reflexivity.
Qed.

Lemma ascii_of_z_148_to_AsciiToZ : forall z c,
  0 <= z <= 127 ->
  ascii_of_z_148 z = c ->
  z = AsciiToZ c.
Proof.
  intros z c Hz Heq.
  unfold ascii_of_z_148 in Heq.
  apply f_equal with (f := nat_of_ascii) in Heq.
  rewrite nat_ascii_embedding in Heq by lia.
  rewrite <- ascii_nat_to_z_148.
  rewrite <- Heq.
  lia.
Qed.

Lemma lit_payload_148_cons : forall c s,
  lit_payload_148 (String c s) = AsciiToZ c :: lit_payload_148 s.
Proof.
  intros c s.
  unfold lit_payload_148, StringToList, StringLength.
  simpl.
  rewrite SuccNat2Pos.id_succ.
  simpl.
  rewrite Nat2Z.id.
  reflexivity.
Qed.

Lemma string_of_list_z_148_inv : forall p s,
  string_lib.valid_string p ->
  string_of_list_z_148 p = s ->
  p = lit_payload_148 s.
Proof.
  induction p as [| c rest IH]; intros s Hvalid Heq.
  - destruct s; simpl in Heq; [| discriminate].
    unfold lit_payload_148, StringLength, StringToList.
    simpl. reflexivity.
  - destruct s as [| sc ss]; simpl in Heq; [discriminate |].
    inversion Heq as [[Hc Hrest]]; subst ss.
    assert (Hc_eq : c = AsciiToZ sc).
    {
      apply ascii_of_z_148_to_AsciiToZ; [| exact Hc].
      destruct Hvalid as [Hascii _].
      specialize (Hascii 0).
      simpl in Hascii.
      apply Hascii.
      rewrite Zlength_cons.
      pose proof (Zlength_nonneg rest).
      lia.
    }
    subst c.
    rewrite Hc.
    rewrite lit_payload_148_cons.
    f_equal.
    apply IH; [| reflexivity].
    destruct Hvalid as [Hascii Hno_nul].
    split.
    + intros i Hi.
      specialize (Hascii (i + 1)).
      rewrite Znth_cons in Hascii by lia.
      replace (i + 1 - 1) with i in Hascii by lia.
      apply Hascii.
      unfold string_lib.string_length in *.
      rewrite Zlength_cons.
      lia.
    + intros i Hi.
      specialize (Hno_nul (i + 1)).
      rewrite Znth_cons in Hno_nul by lia.
      replace (i + 1 - 1) with i in Hno_nul by lia.
      apply Hno_nul.
      unfold string_lib.string_length in *.
      rewrite Zlength_cons.
      lia.
Qed.

Lemma get_planet_index_range_148 : forall s n,
  get_planet_index s = Some n ->
  (n < 8)%nat.
Proof.
  intros s n H.
  unfold get_planet_index, solar_system in H.
  cbn [fold_left snd] in H.
  repeat
    match type of H with
    | context[String.eqb ?a ?b] => destruct (String.eqb a b) eqn:?
    end;
    inversion H; subst; simpl; lia.
Qed.

Lemma planet_index_z_148_range : forall p,
  planet_index_z_148 p = -1 \/ 0 <= planet_index_z_148 p <= 7.
Proof.
  intros p.
  unfold planet_index_z_148.
  destruct (get_planet_index (string_of_list_z_148 p)) as [n|] eqn:Hidx.
  - right.
    pose proof (get_planet_index_range_148 _ _ Hidx).
    lia.
  - left. reflexivity.
Qed.

Lemma planet_index_z_payload_148 : forall i,
  0 <= i <= 7 ->
  planet_index_z_148 (planet_payload_148 i) = i.
Proof.
  intros i Hi.
  destruct_planet_index_148 i Hi;
    unfold planet_index_z_148, planet_payload_148, lit_payload_148,
      planet_literal_148, mercury_literal_148, venus_literal_148,
      earth_literal_148, mars_literal_148, jupiter_literal_148,
      saturn_literal_148, uranus_literal_148, neptune_literal_148;
    vm_compute; reflexivity.
Qed.

Lemma planet_index_z_to_payload_148 : forall p i,
  string_lib.valid_string p ->
  0 <= i <= 7 ->
  planet_index_z_148 p = i ->
  p = planet_payload_148 i.
Proof.
  intros p i Hvalid Hi Hidx.
  unfold planet_index_z_148 in Hidx.
  destruct (get_planet_index (string_of_list_z_148 p)) as [n|] eqn:Hget;
    [| lia].
  assert (Hn : n = Z.to_nat i) by lia.
  subst n.
  unfold get_planet_index, solar_system in Hget.
  cbn [fold_left snd] in Hget.
  destruct_planet_index_148 i Hi;
    repeat
      match type of Hget with
      | context[String.eqb ?a ?b] => destruct (String.eqb a b) eqn:?
      end;
    inversion Hget; subst;
    try discriminate;
    match goal with
    | H : String.eqb ?lit (string_of_list_z_148 p) = true |- _ =>
        apply String.eqb_eq in H;
        symmetry in H;
        apply string_of_list_z_148_inv in H; [exact H | exact Hvalid]
    end.
Qed.

Lemma planet_scan_state_148_init : forall p,
  planet_scan_state_148 p 0 (-1).
Proof.
  intros p.
  unfold planet_scan_state_148.
  repeat split; try lia.
  destruct (planet_index_z_148_range p) as [Hidx | Hidx].
  - left. split; lia.
  - right. split; [lia | left; lia].
Qed.

Lemma planet_scan_state_148_final : forall p k pos,
  planet_scan_state_148 p k pos ->
  k >= 8 ->
  pos = planet_index_z_148 p.
Proof.
  intros p k pos Hstate Hk.
  unfold planet_scan_state_148 in Hstate.
  destruct Hstate as [Hkb [Hpos [[Hidx Hpos_eq] | [Hidx [[Hbefore Hpos_eq] | [Hafter Hpos_eq]]]]]];
    lia.
Qed.

Lemma planet_scan_state_148_invalid : forall p k pos,
  planet_scan_state_148 p k pos ->
  k >= 8 ->
  pos = -1 ->
  planet_index_z_148 p = -1.
Proof.
  intros p k pos Hstate Hk Hpos_eq.
  pose proof (planet_scan_state_148_final _ _ _ Hstate Hk).
  lia.
Qed.

Lemma planet_scan_state_148_step_hit : forall p m pos,
  string_lib.valid_string p ->
  0 <= m < 8 ->
  planet_scan_state_148 p m pos ->
  p = planet_payload_148 m ->
  planet_scan_state_148 p (m + 1) m.
Proof.
  intros p m pos _ Hm _ Hp.
  subst p.
  pose proof (planet_index_z_payload_148 m ltac:(lia)) as Hidx.
  unfold planet_scan_state_148.
  split; [lia |].
  split; [lia |].
  right.
  split; [lia | right; lia].
Qed.

Lemma planet_scan_state_148_step_miss : forall p m pos,
  string_lib.valid_string p ->
  0 <= m < 8 ->
  planet_scan_state_148 p m pos ->
  p <> planet_payload_148 m ->
  planet_scan_state_148 p (m + 1) pos.
Proof.
  intros p m pos Hvalid Hm Hstate Hneq.
  unfold planet_scan_state_148 in *.
  destruct Hstate as [Hkb [Hpos [[Hidx Hpos_eq] | [Hidx [[Hbefore Hpos_eq] | [Hafter Hpos_eq]]]]]].
  - split; [lia |].
    split; [lia |].
    left. split; lia.
  - split; [lia |].
    split; [lia |].
    right. split; [lia |].
    destruct (Z.eq_dec (planet_index_z_148 p) m) as [Heq | Hne].
    + exfalso.
      apply Hneq.
      apply planet_index_z_to_payload_148; try lia; exact Hvalid.
    + left. lia.
  - split; [lia |].
    split; [lia |].
    right. split; [lia | right; lia].
Qed.

Lemma strcmp_result_zero_eq_148 : forall a b,
  string_lib.valid_string a ->
  string_lib.valid_string b ->
  string_lib.strcmp_result a b 0 ->
  a = b.
Proof.
  intros a b Hva Hvb Hcmp.
  unfold string_lib.strcmp_result in Hcmp.
  destruct Hcmp as [i [Hi1 [Hi2 [Hpref [Hret Hstop]]]]].
  assert (Heq_i :
    Znth i (string_lib.c_string a) 0 =
    Znth i (string_lib.c_string b) 0) by lia.
  destruct Hstop as [Ha0 | Hdiff]; [| contradiction].
  assert (Hi_len_a : i = string_lib.string_length a)
    by (eapply string_lib.c_string_zero_index_eq_length; eauto; lia).
  assert (Hb0 : Znth i (string_lib.c_string b) 0 = 0) by lia.
  assert (Hi_len_b : i = string_lib.string_length b)
    by (eapply string_lib.c_string_zero_index_eq_length; eauto; lia).
  apply list_eq_ext with (d := 0).
  split.
  - unfold string_lib.string_length in *; lia.
  - intros k Hk.
    assert (Hki : 0 <= k < i)
      by (unfold string_lib.string_length in Hi_len_a; lia).
    specialize (Hpref k Hki).
    rewrite !string_lib.c_string_Znth_inside in Hpref
      by (unfold string_lib.string_length in *; lia).
    exact Hpref.
Qed.

Lemma strcmp_result_same_zero_148 : forall a ret,
  string_lib.strcmp_result a a ret ->
  ret = 0.
Proof.
  intros a ret Hcmp.
  unfold string_lib.strcmp_result in Hcmp.
  destruct Hcmp as [i [_ [_ [_ [Hret _]]]]].
  lia.
Qed.

Lemma strcmp_result_nonzero_neq_148 : forall a b ret,
  string_lib.strcmp_result a b ret ->
  ret <> 0 ->
  a <> b.
Proof.
  intros a b ret Hcmp Hret Hsame.
  subst b.
  apply Hret.
  exact (strcmp_result_same_zero_148 a ret Hcmp).
Qed.

Lemma planet_scan_state_148_step_hit_strcmp : forall p m pos ret,
  string_lib.valid_string p ->
  0 <= m < 8 ->
  planet_scan_state_148 p m pos ->
  string_lib.strcmp_result (planet_payload_148 m) p ret ->
  ret = 0 ->
  planet_scan_state_148 p (m + 1) m.
Proof.
  intros p m pos ret Hvalid Hm Hstate Hcmp Hret.
  eapply planet_scan_state_148_step_hit with (pos := pos).
  - exact Hvalid.
  - exact Hm.
  - exact Hstate.
  - symmetry.
    eapply strcmp_result_zero_eq_148.
    + apply planet_payload_valid_string_148; lia.
    + exact Hvalid.
    + rewrite <- Hret. exact Hcmp.
Qed.

Lemma planet_scan_state_148_step_miss_strcmp : forall p m pos ret,
  string_lib.valid_string p ->
  0 <= m < 8 ->
  planet_scan_state_148 p m pos ->
  string_lib.strcmp_result (planet_payload_148 m) p ret ->
  ret <> 0 ->
  planet_scan_state_148 p (m + 1) pos.
Proof.
  intros p m pos ret Hvalid Hm Hstate Hcmp Hret.
  eapply planet_scan_state_148_step_miss with (pos := pos).
  - exact Hvalid.
  - exact Hm.
  - exact Hstate.
  - intro Hp.
    apply Hret.
    subst p.
    exact (strcmp_result_same_zero_148 (planet_payload_148 m) ret Hcmp).
Qed.

Lemma mercury_lit_to_store_148 : forall LM,
  store_stringLit (LM mercury_literal_148) mercury_literal_148 |--
  string_lib.store_string (planet_ptr_148 LM 0) (planet_payload_148 0).
Proof.
  intros.
  unfold store_stringLit, string_lib.store_string.
  unfold planet_ptr_148, planet_payload_148, planet_literal_148, lit_payload_148.
  unfold mercury_literal_148.
  simpl.
  entailer!.
Qed.

Lemma venus_lit_to_store_148 : forall LM,
  store_stringLit (LM venus_literal_148) venus_literal_148 |--
  string_lib.store_string (planet_ptr_148 LM 1) (planet_payload_148 1).
Proof.
  intros.
  unfold store_stringLit, string_lib.store_string.
  unfold planet_ptr_148, planet_payload_148, planet_literal_148, lit_payload_148.
  unfold venus_literal_148.
  simpl.
  entailer!.
Qed.

Lemma earth_lit_to_store_148 : forall LM,
  store_stringLit (LM earth_literal_148) earth_literal_148 |--
  string_lib.store_string (planet_ptr_148 LM 2) (planet_payload_148 2).
Proof.
  intros.
  unfold store_stringLit, string_lib.store_string.
  unfold planet_ptr_148, planet_payload_148, planet_literal_148, lit_payload_148.
  unfold earth_literal_148.
  simpl.
  entailer!.
Qed.

Lemma mars_lit_to_store_148 : forall LM,
  store_stringLit (LM mars_literal_148) mars_literal_148 |--
  string_lib.store_string (planet_ptr_148 LM 3) (planet_payload_148 3).
Proof.
  intros.
  unfold store_stringLit, string_lib.store_string.
  unfold planet_ptr_148, planet_payload_148, planet_literal_148, lit_payload_148.
  unfold mars_literal_148.
  simpl.
  entailer!.
Qed.

Lemma jupiter_lit_to_store_148 : forall LM,
  store_stringLit (LM jupiter_literal_148) jupiter_literal_148 |--
  string_lib.store_string (planet_ptr_148 LM 4) (planet_payload_148 4).
Proof.
  intros.
  unfold store_stringLit, string_lib.store_string.
  unfold planet_ptr_148, planet_payload_148, planet_literal_148, lit_payload_148.
  unfold jupiter_literal_148.
  simpl.
  entailer!.
Qed.

Lemma saturn_lit_to_store_148 : forall LM,
  store_stringLit (LM saturn_literal_148) saturn_literal_148 |--
  string_lib.store_string (planet_ptr_148 LM 5) (planet_payload_148 5).
Proof.
  intros.
  unfold store_stringLit, string_lib.store_string.
  unfold planet_ptr_148, planet_payload_148, planet_literal_148, lit_payload_148.
  unfold saturn_literal_148.
  simpl.
  entailer!.
Qed.

Lemma uranus_lit_to_store_148 : forall LM,
  store_stringLit (LM uranus_literal_148) uranus_literal_148 |--
  string_lib.store_string (planet_ptr_148 LM 6) (planet_payload_148 6).
Proof.
  intros.
  unfold store_stringLit, string_lib.store_string.
  unfold planet_ptr_148, planet_payload_148, planet_literal_148, lit_payload_148.
  unfold uranus_literal_148.
  simpl.
  entailer!.
Qed.

Lemma neptune_lit_to_store_148 : forall LM,
  store_stringLit (LM neptune_literal_148) neptune_literal_148 |--
  string_lib.store_string (planet_ptr_148 LM 7) (planet_payload_148 7).
Proof.
  intros.
  unfold store_stringLit, string_lib.store_string.
  unfold planet_ptr_148, planet_payload_148, planet_literal_148, lit_payload_148.
  unfold neptune_literal_148.
  simpl.
  entailer!.
Qed.

Lemma output_state_148_init : forall LM lo hi,
  output_state_148 LM lo hi 0 [] [].
Proof.
  intros.
  unfold output_state_148, selected_indices_prefix_148, candidate_prefix_148.
  simpl. repeat split; lia.
Qed.

Lemma output_state_148_at_lower_empty : forall LM lo hi,
  0 <= lo <= 7 ->
  output_state_148 LM lo hi lo [] [].
Proof.
  intros LM lo hi Hlo.
  unfold output_state_148, selected_indices_prefix_148, candidate_prefix_148,
    index_between_148, candidate_indices_148.
  repeat split; try lia;
    assert (lo = 0 \/ lo = 1 \/ lo = 2 \/ lo = 3 \/
            lo = 4 \/ lo = 5 \/ lo = 6 \/ lo = 7) as Hcases by lia;
    repeat (destruct Hcases as [Hcases | Hcases];
            [subst; simpl; reflexivity |]);
    subst; simpl; reflexivity.
Qed.

Lemma output_state_148_Zlength : forall LM lo hi k rows ptrs,
  output_state_148 LM lo hi k rows ptrs ->
  Zlength rows = Zlength ptrs.
Proof.
  intros LM lo hi k rows ptrs [_ [Hrows Hptrs]].
  subst.
  repeat rewrite Zlength_correct.
  repeat rewrite map_length.
  reflexivity.
Qed.

Lemma selected_indices_prefix_148_step : forall lo hi m,
  1 <= m <= 6 ->
  lo < m ->
  m < hi ->
  selected_indices_prefix_148 lo hi m =
  selected_indices_prefix_148 lo hi (m - 1) ++ [m].
Proof.
  intros lo hi m Hm Hlo Hhi.
  assert (Hlo_bool : Z.ltb lo m = true) by (apply Z.ltb_lt; lia).
  assert (Hhi_bool : Z.ltb m hi = true) by (apply Z.ltb_lt; lia).
  assert (m = 1 \/ m = 2 \/ m = 3 \/ m = 4 \/
          m = 5 \/ m = 6) as Hcases by lia.
  repeat (destruct Hcases as [Hcases | Hcases]; [subst m |]);
    try subst m;
    unfold selected_indices_prefix_148, candidate_prefix_148,
      candidate_indices_148, index_between_148;
    simpl in *;
    rewrite Hlo_bool, Hhi_bool;
    simpl;
    repeat match goal with
    | |- context[Z.ltb ?x ?y] => destruct (Z.ltb x y)
    end;
    reflexivity.
Qed.

Lemma output_state_148_step : forall LM lo hi m rows ptrs,
  0 <= lo <= 7 ->
  0 <= hi <= 7 ->
  lo < m ->
  m < hi ->
  output_state_148 LM lo hi (m - 1) rows ptrs ->
  output_state_148 LM lo hi m
    (rows ++ [planet_payload_148 m])
    (ptrs ++ [planet_ptr_148 LM m]).
Proof.
  intros LM lo hi m rows ptrs Hlo Hhi Hlo_m Hm_hi Hstate.
  destruct Hstate as [Hk [Hrows Hptrs]].
  assert (1 <= m <= 6) by lia.
  unfold output_state_148.
  repeat split; try lia.
  - rewrite Hrows.
    rewrite (selected_indices_prefix_148_step lo hi m) by lia.
    rewrite map_app. reflexivity.
  - rewrite Hptrs.
    rewrite (selected_indices_prefix_148_step lo hi m) by lia.
    rewrite map_app. reflexivity.
Qed.

Lemma output_state_148_ptrs_length_before_lt_6 :
  forall LM lo hi m rows ptrs,
  0 <= hi <= 7 ->
  m < hi ->
  output_state_148 LM lo hi (m - 1) rows ptrs ->
  Zlength ptrs < 6.
Proof.
  intros LM lo hi m rows ptrs Hhi Hm_hi Hstate.
  destruct Hstate as [Hk [_ Hptrs]].
  subst ptrs.
  assert (m = 1 \/ m = 2 \/ m = 3 \/ m = 4 \/
          m = 5 \/ m = 6) as Hcases by lia.
  repeat (destruct Hcases as [Hcases | Hcases]; [subst m |]);
    try subst m;
    unfold selected_indices_prefix_148, candidate_prefix_148,
      candidate_indices_148, index_between_148;
    simpl;
    repeat match goal with
    | |- context[Z.ltb ?x ?y] => destruct (Z.ltb x y)
    end;
    repeat rewrite Zlength_correct;
    repeat rewrite map_length;
    simpl; lia.
Qed.

Lemma get_planet_index_literal_148 : forall s n,
  get_planet_index s = Some n ->
  s = planet_literal_148 (Z.of_nat n).
Proof.
  intros s n H.
  unfold get_planet_index, solar_system in H.
  cbn [fold_left snd] in H.
  repeat
    match type of H with
    | context[String.eqb ?a ?b] =>
        destruct (String.eqb a b) eqn:?
    end;
    inversion H; subst; simpl;
    match goal with
    | H : String.eqb ?lit s = true |- _ =>
        symmetry; apply String.eqb_eq; exact H
    end.
Qed.

Lemma selected_indices_prefix_148_done : forall lo hi k,
  0 <= lo <= 7 ->
  0 <= hi <= 7 ->
  lo < hi ->
  hi - 1 <= k <= 7 ->
  selected_indices_prefix_148 lo hi k = selected_indices_prefix_148 lo hi 6.
Proof.
  intros lo hi k Hlo Hhi Hlt Hk.
  destruct_planet_index_148 lo Hlo;
    destruct_planet_index_148 hi Hhi;
    assert (0 <= k <= 7) as Hk_range by lia;
    destruct_planet_index_148 k Hk_range;
    try lia;
    unfold selected_indices_prefix_148, candidate_prefix_148,
      candidate_indices_148, index_between_148;
    simpl; reflexivity.
Qed.

Lemma output_state_148_done : forall LM p1 p2 lo hi m rows ptrs,
  0 <= planet_index_z_148 p1 <= 7 ->
  0 <= planet_index_z_148 p2 <= 7 ->
  0 <= lo <= 7 ->
  0 <= hi <= 7 ->
  lo < hi ->
  lo = planet_min_index_148 (planet_index_z_148 p1) (planet_index_z_148 p2) ->
  hi = planet_max_index_148 (planet_index_z_148 p1) (planet_index_z_148 p2) ->
  hi <= m ->
  m <= hi + 1 ->
  output_state_148 LM lo hi (m - 1) rows ptrs ->
  rows = planet_between_rows_148 (planet_index_z_148 p1) (planet_index_z_148 p2) /\
  ptrs = planet_between_ptrs_148 LM (planet_index_z_148 p1) (planet_index_z_148 p2).
Proof.
  intros LM p1 p2 lo hi m rows ptrs Hidx1 Hidx2 Hlo Hhi Hlt
    Hlo_eq Hhi_eq Hm_hi Hm_bound Hstate.
  destruct Hstate as [Hk [Hrows Hptrs]].
  subst rows ptrs.
  remember (planet_index_z_148 p1) as i.
  remember (planet_index_z_148 p2) as j.
  destruct_planet_index_148 i ltac:(lia);
    destruct_planet_index_148 j ltac:(lia);
    repeat match goal with
    | H : planet_index_z_148 _ = _ |- _ => rewrite H in *
    end;
    unfold planet_min_index_148, planet_max_index_148 in Hlo_eq, Hhi_eq;
    simpl in Hlo_eq, Hhi_eq;
    subst lo hi;
    try lia;
    split;
    unfold planet_between_rows_148, planet_between_ptrs_148,
      selected_indices_148, valid_planet_index_148, between_bounds_148;
    simpl;
    rewrite selected_indices_prefix_148_done with (k := m - 1);
    try lia;
    reflexivity.
Qed.

Lemma output_state_148_done_le : forall LM p1 p2 lo hi m rows ptrs,
  0 <= planet_index_z_148 p1 <= 7 ->
  0 <= planet_index_z_148 p2 <= 7 ->
  0 <= lo <= 7 ->
  0 <= hi <= 7 ->
  lo <= hi ->
  lo = planet_min_index_148 (planet_index_z_148 p1) (planet_index_z_148 p2) ->
  hi = planet_max_index_148 (planet_index_z_148 p1) (planet_index_z_148 p2) ->
  hi <= m ->
  m <= hi + 1 ->
  output_state_148 LM lo hi (m - 1) rows ptrs ->
  rows = planet_between_rows_148 (planet_index_z_148 p1) (planet_index_z_148 p2) /\
  ptrs = planet_between_ptrs_148 LM (planet_index_z_148 p1) (planet_index_z_148 p2).
Proof.
  intros LM p1 p2 lo hi m rows ptrs Hidx1 Hidx2 Hlo Hhi Hle
    Hlo_eq Hhi_eq Hm_hi Hm_bound Hstate.
  destruct (Z.eq_dec lo hi) as [Heq | Hneq].
  - destruct Hstate as [Hk [Hrows Hptrs]].
    subst rows ptrs hi.
    remember (planet_index_z_148 p1) as i.
    remember (planet_index_z_148 p2) as j.
    destruct_planet_index_148 i ltac:(lia);
      destruct_planet_index_148 j ltac:(lia);
      repeat match goal with
      | H : planet_index_z_148 _ = _ |- _ => rewrite H in *
      end;
      unfold planet_min_index_148, planet_max_index_148 in *;
      simpl in *;
      subst lo;
      assert (m = 0 \/ m = 1 \/ m = 2 \/ m = 3 \/
              m = 4 \/ m = 5 \/ m = 6 \/ m = 7 \/ m = 8) as Hm_cases by lia;
      repeat (destruct Hm_cases as [Hm_cases | Hm_cases];
              [subst m |]);
      try subst m;
      try lia;
      split;
      unfold planet_between_rows_148, planet_between_ptrs_148,
        selected_indices_148, valid_planet_index_148, between_bounds_148,
        selected_indices_prefix_148, candidate_prefix_148,
        candidate_indices_148, index_between_148;
      simpl; reflexivity.
  - eapply output_state_148_done with (lo := lo) (hi := hi) (m := m);
      try eassumption; lia.
Qed.

Lemma planet_between_rows_ptrs_Zlength_148 : forall LM i j,
  Zlength (planet_between_rows_148 i j) =
  Zlength (planet_between_ptrs_148 LM i j).
Proof.
  intros.
  unfold planet_between_rows_148, planet_between_ptrs_148.
  repeat rewrite Zlength_correct.
  repeat rewrite map_length.
  reflexivity.
Qed.

Lemma planet_between_rows_Zlength_bound_148 : forall i j,
  Zlength (planet_between_rows_148 i j) <= 6.
Proof.
  intros i j.
  unfold planet_between_rows_148.
  rewrite Zlength_correct, map_length.
  unfold selected_indices_148.
  destruct (valid_planet_index_148 i && valid_planet_index_148 j)%bool.
  - destruct (between_bounds_148 i j) as [lo hi].
    unfold selected_indices_prefix_148, candidate_prefix_148,
      candidate_indices_148.
    simpl.
    repeat match goal with
    | |- context[index_between_148 lo hi ?x] =>
        destruct (index_between_148 lo hi x)
    end;
    simpl; lia.
  - simpl. lia.
Qed.

Lemma planet_between_rows_invalid_left_148 : forall p j,
  planet_index_z_148 p = -1 ->
  planet_between_rows_148 (planet_index_z_148 p) j = [] /\
  planet_between_ptrs_148 LitMap (planet_index_z_148 p) j = [].
Proof.
  intros p j Hidx.
  rewrite Hidx.
  unfold planet_between_rows_148, planet_between_ptrs_148,
    selected_indices_148, valid_planet_index_148.
  simpl. split; reflexivity.
Qed.

Lemma planet_between_rows_invalid_right_148 : forall i p,
  planet_index_z_148 p = -1 ->
  planet_between_rows_148 i (planet_index_z_148 p) = [] /\
  planet_between_ptrs_148 LitMap i (planet_index_z_148 p) = [].
Proof.
  intros i p Hidx.
  rewrite Hidx.
  unfold planet_between_rows_148, planet_between_ptrs_148,
    selected_indices_148, valid_planet_index_148.
  destruct (Z.leb 0 i && Z.leb i 7)%bool; simpl; split; reflexivity.
Qed.

Ltac solve_problem_148_member_forward :=
  repeat match goal with
  | H : False |- _ => contradiction
  | H : _ \/ _ |- _ => destruct H as [H | H]
  | H : _ = _ |- _ => subst
  end;
  repeat eexists;
  repeat split;
  try reflexivity;
  simpl; lia.

Ltac solve_problem_148_member_backward :=
  match goal with
  | H : exists idx, _ |- _ =>
      destruct H as [idx [Hidx Hbounds]];
      repeat
        (destruct idx as [| idx]; simpl in Hbounds; try lia);
      pose proof (get_planet_index_literal_148 _ _ Hidx);
      subst; simpl; auto
  end.

Ltac solve_problem_148_sorted :=
  intros p_a p_b i j Hi Hj Hij;
  repeat (destruct i as [| i]; simpl in Hi; try discriminate);
  repeat (destruct j as [| j]; simpl in Hj; try discriminate);
  inversion Hi; inversion Hj; subst; clear Hi Hj;
  repeat eexists;
  repeat split;
  try reflexivity;
  simpl; lia.

Ltac solve_problem_148_spec_concrete :=
  cbv - [nth_error get_planet_index];
  repeat match goal with
  | H : _ |- _ => progress cbn in H
  | |- _ => progress cbn
  end;
  repeat match goal with
  | |- _ /\ _ => split
  | |- forall _, _ => intro
  | |- _ <-> _ => split
  | H : _ /\ _ |- _ => destruct H
  | H : exists _, _ |- _ => destruct H
  | H : _ \/ _ |- _ => destruct H
  | H : False |- _ => contradiction
  | H : nth_error ?xs ?n = Some _ |- _ =>
      destruct n; cbn [nth_error] in H; try discriminate
  | H : get_planet_index ?p = Some ?idx |- _ =>
      pose proof (get_planet_index_literal_148 _ _ H); subst p
  | H : Some _ = Some _ |- _ => inversion H; subst; clear H
  | H : None = Some _ |- _ => discriminate
  | H : Some _ = None |- _ => discriminate
  | H : ?x = ?x |- _ => clear H
  | H : _ = _ |- _ => subst
  | |- context[planet_literal_148 (Z.of_nat ?n)] =>
      let Hcases := fresh "Hcases" in
      assert (n = 0%nat \/ n = 1%nat \/ n = 2%nat \/ n = 3%nat \/
              n = 4%nat \/ n = 5%nat \/ n = 6%nat \/ n = 7%nat) as Hcases by lia;
      repeat (destruct Hcases as [Hcases | Hcases];
              [subst n; simpl in *; try solve [auto | lia] |]);
      subst n; simpl in *; try solve [auto | lia]
  | H : context[
      (fix Ffix (xs : list string) (n : nat) {struct n} : option string :=
        match n with
        | O =>
            match xs with
            | [] => None
            | x :: _ => Some x
            end
        | S n' =>
            match xs with
            | [] => None
            | _ :: xs' => Ffix xs' n'
            end
        end) ?xs ?n] |- _ =>
      destruct n; simpl in H; try discriminate
  | H : context[match ?n with O => _ | S _ => _ end] |- _ =>
      lazymatch type of n with
      | nat => destruct n; simpl in H; try discriminate
      end
  end;
  repeat match goal with
  | H : _ |- _ => progress cbn in H
  | |- _ => progress cbn
  end;
  try solve
    [ repeat eexists; repeat split; simpl; try reflexivity; try (vm_compute; reflexivity); lia
    | simpl; tauto
    | congruence
    | lia ];
  try match goal with
  | |- context[planet_literal_148 (Z.of_nat ?x)] =>
      repeat
        (destruct x; simpl in *; try solve [auto | lia])
  end;
  try solve
    [ unfold mercury_literal_148, venus_literal_148, earth_literal_148,
        mars_literal_148, jupiter_literal_148, saturn_literal_148,
        uranus_literal_148, neptune_literal_148 in *;
      simpl in *;
      repeat (first [left; reflexivity | right]) ].

Lemma problem_148_spec_z_between_valid_148 : forall p1 p2,
  string_lib.valid_string p1 ->
  string_lib.valid_string p2 ->
  0 <= planet_index_z_148 p1 <= 7 ->
  0 <= planet_index_z_148 p2 <= 7 ->
  problem_148_spec_z p1 p2
    (planet_between_rows_148 (planet_index_z_148 p1) (planet_index_z_148 p2)).
Proof.
  intros p1 p2 Hvalid1 Hvalid2 Hidx1 Hidx2.
  remember (planet_index_z_148 p1) as i.
  remember (planet_index_z_148 p2) as j.
  symmetry in Heqi, Heqj.
  pose proof (planet_index_z_to_payload_148 p1 i Hvalid1 Hidx1 Heqi) as Hp1.
  pose proof (planet_index_z_to_payload_148 p2 j Hvalid2 Hidx2 Heqj) as Hp2.
  subst p1 p2.
  destruct_planet_index_148 i Hidx1;
    destruct_planet_index_148 j Hidx2;
    solve_problem_148_spec_concrete.
Qed.

Lemma planet_index_z_148_get_none : forall p,
  planet_index_z_148 p = -1 ->
  get_planet_index (string_of_list_z_148 p) = None.
Proof.
  intros p Hidx.
  unfold planet_index_z_148 in Hidx.
  destruct (get_planet_index (string_of_list_z_148 p)); [lia | reflexivity].
Qed.

Lemma problem_148_spec_z_invalid_left_148 : forall p1 p2,
  planet_index_z_148 p1 = -1 ->
  problem_148_spec_z p1 p2 [].
Proof.
  intros p1 p2 Hidx.
  unfold problem_148_spec_z, problem_148_spec.
  rewrite planet_index_z_148_get_none by exact Hidx.
  reflexivity.
Qed.

Lemma problem_148_spec_z_invalid_right_148 : forall p1 p2,
  planet_index_z_148 p2 = -1 ->
  problem_148_spec_z p1 p2 [].
Proof.
  intros p1 p2 Hidx.
  unfold problem_148_spec_z, problem_148_spec.
  rewrite planet_index_z_148_get_none with (p := p2) by exact Hidx.
  destruct (get_planet_index (string_of_list_z_148 p1)); reflexivity.
Qed.
End MigratedCompanionProofs.
Export MigratedCompanionProofs.
(* END migrated companion-spec proofs *)

Ltac solve_scan_state_148 :=
  match goal with
  | |- planet_scan_state_148 ?p (?m + 1) ?pos =>
      match goal with
      | Hcmp : strcmp_result (planet_payload_148 ?i) p ?ret |- _ =>
          first
            [ match goal with
              | Hstate : planet_scan_state_148 p m pos |- _ =>
                  assert (m = i) by lia; subst m;
                  eapply planet_scan_state_148_step_miss_strcmp;
                  [ eassumption | lia | eassumption | exact Hcmp | lia ]
              end
            | match goal with
              | Hstate : planet_scan_state_148 p m ?old_pos |- _ =>
                  replace pos with m by lia;
                  assert (m = i) by lia; subst m;
                  eapply planet_scan_state_148_step_hit_strcmp;
                  [ eassumption | lia | eassumption | exact Hcmp | lia ]
              end ]
      end
  end.

Ltac solve_planet_literals_heap_148 :=
  right;
  pre_process_default;
  let Hsafe := fresh "Hplanet_payloads_string_safe_148" in
  pose proof planet_payloads_string_safe_148_proof as Hsafe;
  repeat match goal with
  | H : ?x = planet_ptr_148 LitMap _ |- _ => subst x
  | H : planet_ptr_148 LitMap _ = ?x |- _ => subst x
  end;
  unfold planet_literals_heap_148, string_lib.store_string;
  entailer!;
  try solve_scan_state_148.

Ltac assert_output_ptrs_before_lt_6_148 :=
  match goal with
  | H : output_state_148 LitMap ?lo ?hi ?k ?rows ?ptrs |- _ =>
      assert (Hlen : Zlength ptrs < 6);
      [ replace k with ((k + 1) - 1) in H by lia;
        eapply output_state_148_ptrs_length_before_lt_6 with (m := k + 1) (rows := rows);
        [lia | lia | exact H]
      | idtac ]
  end.

Ltac pose_scan_finals_148 :=
  match goal with
  | H1 : planet_scan_state_148 ?p1 ?m ?pos1,
    H2 : planet_scan_state_148 ?p2 ?m ?pos2 |- _ =>
      pose proof (planet_scan_state_148_final p1 m pos1 H1 ltac:(lia));
      pose proof (planet_scan_state_148_final p2 m pos2 H2 ltac:(lia))
  end.

Ltac assert_min_max_148 :=
  match goal with
  | Hgt : ?pos1 > ?pos2,
    Hpos1 : ?pos1 = planet_index_z_148 ?p1,
    Hpos2 : ?pos2 = planet_index_z_148 ?p2 |- _ =>
      assert (pos2 =
        planet_min_index_148 (planet_index_z_148 p1) (planet_index_z_148 p2))
        by (rewrite <- Hpos1, <- Hpos2;
            unfold planet_min_index_148; destruct (Z.leb_spec0 pos1 pos2); lia);
      assert (pos1 =
        planet_max_index_148 (planet_index_z_148 p1) (planet_index_z_148 p2))
        by (rewrite <- Hpos1, <- Hpos2;
            unfold planet_max_index_148; destruct (Z.leb_spec0 pos1 pos2); lia)
  | Hle : ?pos1 <= ?pos2,
    Hpos1 : ?pos1 = planet_index_z_148 ?p1,
    Hpos2 : ?pos2 = planet_index_z_148 ?p2 |- _ =>
      assert (pos1 =
        planet_min_index_148 (planet_index_z_148 p1) (planet_index_z_148 p2))
        by (rewrite <- Hpos1, <- Hpos2;
            unfold planet_min_index_148; destruct (Z.leb_spec0 pos1 pos2); lia);
      assert (pos2 =
        planet_max_index_148 (planet_index_z_148 p1) (planet_index_z_148 p2))
        by (rewrite <- Hpos1, <- Hpos2;
            unfold planet_max_index_148; destruct (Z.leb_spec0 pos1 pos2); lia)
  end.









Lemma proof_of_bf_entail_wit_1 : bf_entail_wit_1.
Proof.
  right.
  pre_process_default.
  pose proof planet_payloads_string_safe_148_proof as Hplanet_payloads_string_safe_148.
  sep_apply_l_atomic (GlobalStrings_split LitMap neptune_literal_148).
  sep_apply_l_atomic (GlobalStrings_missing_split LitMap (neptune_literal_148 :: nil) uranus_literal_148).
  { entailer!. vm_compute. intros [H|[]]; discriminate H. }
  sep_apply_l_atomic (GlobalStrings_missing_split LitMap (uranus_literal_148 :: neptune_literal_148 :: nil) saturn_literal_148).
  { entailer!. vm_compute. intros [H|[H|[]]]; discriminate H. }
  sep_apply_l_atomic (GlobalStrings_missing_split LitMap (saturn_literal_148 :: uranus_literal_148 :: neptune_literal_148 :: nil) jupiter_literal_148).
  { entailer!. vm_compute. intros [H|[H|[H|[]]]]; discriminate H. }
  sep_apply_l_atomic (GlobalStrings_missing_split LitMap (jupiter_literal_148 :: saturn_literal_148 :: uranus_literal_148 :: neptune_literal_148 :: nil) mars_literal_148).
  { entailer!. vm_compute. intros [H|[H|[H|[H|[]]]]]; discriminate H. }
  sep_apply_l_atomic (GlobalStrings_missing_split LitMap (mars_literal_148 :: jupiter_literal_148 :: saturn_literal_148 :: uranus_literal_148 :: neptune_literal_148 :: nil) earth_literal_148).
  { entailer!. vm_compute. intros [H|[H|[H|[H|[H|[]]]]]]; discriminate H. }
  sep_apply_l_atomic (GlobalStrings_missing_split LitMap (earth_literal_148 :: mars_literal_148 :: jupiter_literal_148 :: saturn_literal_148 :: uranus_literal_148 :: neptune_literal_148 :: nil) venus_literal_148).
  { entailer!. vm_compute. intros [H|[H|[H|[H|[H|[H|[]]]]]]]; discriminate H. }
  sep_apply_l_atomic (GlobalStrings_missing_split LitMap (venus_literal_148 :: earth_literal_148 :: mars_literal_148 :: jupiter_literal_148 :: saturn_literal_148 :: uranus_literal_148 :: neptune_literal_148 :: nil) mercury_literal_148).
  { entailer!. vm_compute. intros [H|[H|[H|[H|[H|[H|[H|[]]]]]]]]; discriminate H. }
  unfold planet_literals_heap_148.
  sep_apply_l_atomic (mercury_lit_to_store_148 LitMap).
  sep_apply_l_atomic (venus_lit_to_store_148 LitMap).
  sep_apply_l_atomic (earth_lit_to_store_148 LitMap).
  sep_apply_l_atomic (mars_lit_to_store_148 LitMap).
  sep_apply_l_atomic (jupiter_lit_to_store_148 LitMap).
  sep_apply_l_atomic (saturn_lit_to_store_148 LitMap).
  sep_apply_l_atomic (uranus_lit_to_store_148 LitMap).
  sep_apply_l_atomic (neptune_lit_to_store_148 LitMap).
  unfold all_planet_literals_148.
  unfold planet_ptr_148, planet_literal_148.
  unfold mercury_literal_148, venus_literal_148, earth_literal_148, mars_literal_148.
  unfold jupiter_literal_148, saturn_literal_148, uranus_literal_148, neptune_literal_148.
  simpl.
  entailer!.
Qed.



Lemma proof_of_bf_entail_wit_2 : bf_entail_wit_2.
Proof.
  right.
  pre_process_default.
  entailer!;
    apply planet_scan_state_148_init.
Qed.

Lemma proof_of_bf_entail_wit_3 : bf_entail_wit_3.
Proof.
  left.
  pre_process_default.
  pose proof planet_payloads_string_safe_148_proof as Hplanet_payloads_string_safe_148.
  subst mercury venus earth mars jupiter saturn uranus neptune.
  unfold planet_literals_heap_148.
  entailer!.
Qed.

Lemma proof_of_bf_entail_wit_4_1 : bf_entail_wit_4_1.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_2 : bf_entail_wit_4_2.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_3 : bf_entail_wit_4_3.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_4 : bf_entail_wit_4_4.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_5 : bf_entail_wit_4_5.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_6 : bf_entail_wit_4_6.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_7 : bf_entail_wit_4_7.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_8 : bf_entail_wit_4_8.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_9 : bf_entail_wit_4_9.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_10 : bf_entail_wit_4_10.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_11 : bf_entail_wit_4_11.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_12 : bf_entail_wit_4_12.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_13 : bf_entail_wit_4_13.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_14 : bf_entail_wit_4_14.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_15 : bf_entail_wit_4_15.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_16 : bf_entail_wit_4_16.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_17 : bf_entail_wit_4_17.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_18 : bf_entail_wit_4_18.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_19 : bf_entail_wit_4_19.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_20 : bf_entail_wit_4_20.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_21 : bf_entail_wit_4_21.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_22 : bf_entail_wit_4_22.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_23 : bf_entail_wit_4_23.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_24 : bf_entail_wit_4_24.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_25 : bf_entail_wit_4_25.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_26 : bf_entail_wit_4_26.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_27 : bf_entail_wit_4_27.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_28 : bf_entail_wit_4_28.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_29 : bf_entail_wit_4_29.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_30 : bf_entail_wit_4_30.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_31 : bf_entail_wit_4_31.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_32 : bf_entail_wit_4_32.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_6_1 : bf_entail_wit_6_1.
Proof.
  left.
  pre_process_default.
  pose_scan_finals_148.
  assert_min_max_148.
  Exists (@nil (list Z)) (@nil Z).
  subst out_size.
  replace (pos2 + 1 - 1) with pos2 by lia.
  assert (Hstate : output_state_148 LitMap pos2 pos1 pos2 (@nil (list Z)) (@nil Z)).
  { apply output_state_148_at_lower_empty; lia. }
  sep_apply_l_atomic (PtrArray.undef_full_to_undef_seg data 6).
  rewrite PtrArray.seg_empty.
  entailer!.
Qed.

Lemma proof_of_bf_entail_wit_6_2 : bf_entail_wit_6_2.
Proof.
  left.
  pre_process_default.
  pose_scan_finals_148.
  assert_min_max_148.
  Exists (@nil (list Z)) (@nil Z).
  subst out_size.
  replace (pos1 + 1 - 1) with pos1 by lia.
  assert (Hstate : output_state_148 LitMap pos1 pos2 pos1 (@nil (list Z)) (@nil Z)).
  { apply output_state_148_at_lower_empty; lia. }
  sep_apply_l_atomic (PtrArray.undef_full_to_undef_seg data 6).
  rewrite PtrArray.seg_empty.
  entailer!.
Qed.

Lemma proof_of_bf_entail_wit_7_1 : bf_entail_wit_7_1.
Proof.
  left.
  pre_process_default.
  assert (m = 1) by lia.
  subst m.
  assert (Hlen : Zlength output_ptrs_2 < 6).
  {
    eapply output_state_148_ptrs_length_before_lt_6
      with (LM := LitMap) (lo := lo) (hi := hi) (m := 1)
           (rows := output_rows_2);
      [lia | lia | match goal with H : output_state_148 _ _ _ _ _ _ |- _ => exact H end].
  }
  Exists output_rows_2 output_ptrs_2.
  entailer!.
Qed.

Lemma proof_of_bf_entail_wit_7_2 : bf_entail_wit_7_2.
Proof.
  left.
  pre_process_default.
  subst m.
  assert (Hlen : Zlength output_ptrs_2 < 6).
  {
    eapply output_state_148_ptrs_length_before_lt_6
      with (LM := LitMap) (lo := lo) (hi := hi) (m := 2)
           (rows := output_rows_2);
      [lia | lia | match goal with H : output_state_148 _ _ _ _ _ _ |- _ => exact H end].
  }
  Exists output_rows_2 output_ptrs_2.
  entailer!.
Qed.

Lemma proof_of_bf_entail_wit_7_3 : bf_entail_wit_7_3.
Proof.
  left.
  pre_process_default.
  subst m.
  assert (Hlen : Zlength output_ptrs_2 < 6).
  {
    eapply output_state_148_ptrs_length_before_lt_6
      with (LM := LitMap) (lo := lo) (hi := hi) (m := 3)
           (rows := output_rows_2);
      [lia | lia | match goal with H : output_state_148 _ _ _ _ _ _ |- _ => exact H end].
  }
  Exists output_rows_2 output_ptrs_2.
  entailer!.
Qed.

Lemma proof_of_bf_entail_wit_7_4 : bf_entail_wit_7_4.
Proof.
  left.
  pre_process_default.
  subst m.
  assert (Hlen : Zlength output_ptrs_2 < 6).
  {
    eapply output_state_148_ptrs_length_before_lt_6
      with (LM := LitMap) (lo := lo) (hi := hi) (m := 4)
           (rows := output_rows_2);
      [lia | lia | match goal with H : output_state_148 _ _ _ _ _ _ |- _ => exact H end].
  }
  Exists output_rows_2 output_ptrs_2.
  entailer!.
Qed.

Lemma proof_of_bf_entail_wit_7_5 : bf_entail_wit_7_5.
Proof.
  left.
  pre_process_default.
  subst m.
  assert (Hlen : Zlength output_ptrs_2 < 6).
  {
    eapply output_state_148_ptrs_length_before_lt_6
      with (LM := LitMap) (lo := lo) (hi := hi) (m := 5)
           (rows := output_rows_2);
      [lia | lia | match goal with H : output_state_148 _ _ _ _ _ _ |- _ => exact H end].
  }
  Exists output_rows_2 output_ptrs_2.
  entailer!.
Qed.

Lemma proof_of_bf_entail_wit_7_6 : bf_entail_wit_7_6.
Proof.
  left.
  pre_process_default.
  subst m.
  assert (Hlen : Zlength output_ptrs_2 < 6).
  {
    eapply output_state_148_ptrs_length_before_lt_6
      with (LM := LitMap) (lo := lo) (hi := hi) (m := 6)
           (rows := output_rows_2);
      [lia | lia | match goal with H : output_state_148 _ _ _ _ _ _ |- _ => exact H end].
  }
  Exists output_rows_2 output_ptrs_2.
  entailer!.
Qed.

Lemma proof_of_bf_entail_wit_8 : bf_entail_wit_8.
Proof.
  left.
  pre_process_default.
  Exists (output_rows_2 ++ (planet_payload_148 m :: nil))
         (output_ptrs_2 ++ (cur :: nil)).
  assert (Hstate :
    output_state_148 LitMap lo hi m
      (output_rows_2 ++ (planet_payload_148 m :: nil))
      (output_ptrs_2 ++ (cur :: nil))).
  {
    match goal with
    | Hcur : cur = planet_ptr_148 LitMap m |- _ => rewrite Hcur
    end.
    eapply output_state_148_step; try lia; eassumption.
  }
  assert (Hlen : out_size + 1 = Zlength (output_ptrs_2 ++ (cur :: nil))).
  {
    match goal with
    | Hout : out_size = Zlength output_ptrs_2 |- _ => rewrite Hout
    end.
    rewrite Zlength_app.
    rewrite Zlength_cons, Zlength_nil.
    lia.
  }
  unfold store_string, string_lib.store_string.
  entailer!.
Qed.

Lemma proof_of_bf_entail_wit_9 : bf_entail_wit_9.
Proof.
  left.
  pre_process_default.
  Exists output_rows_2 output_ptrs_2.
  replace (m + 1 - 1) with m by lia.
  entailer!.
Qed.








Lemma proof_of_bf_return_wit_1 : bf_return_wit_1.
Proof.
  right.
  pre_process_default.
  assert (Hidx1 : 0 <= planet_index_z_148 p1 <= 7).
  {
    destruct (planet_index_z_148_range p1) as [Hbad | Hok]; [| exact Hok].
    rewrite Hbad in *.
    unfold planet_min_index_148 in *.
    destruct (Z.leb_spec0 (-1) (planet_index_z_148 p2)); lia.
  }
  assert (Hidx2 : 0 <= planet_index_z_148 p2 <= 7).
  {
    destruct (planet_index_z_148_range p2) as [Hbad | Hok]; [| exact Hok].
    rewrite Hbad in *.
    unfold planet_min_index_148 in *.
    destruct (Z.leb_spec0 (planet_index_z_148 p1) (-1)); lia.
  }
  assert (Hle : lo <= hi).
  {
    match goal with
    | Hlo : lo = planet_min_index_148 _ _,
      Hhi : hi = planet_max_index_148 _ _ |- _ =>
        rewrite Hlo, Hhi;
        unfold planet_min_index_148, planet_max_index_148;
        destruct (Z.leb_spec0 (planet_index_z_148 p1) (planet_index_z_148 p2)); lia
    end.
  }
  pose proof (output_state_148_done_le LitMap p1 p2 lo hi m
    output_rows_2 output_ptrs_2 Hidx1 Hidx2 ltac:(lia) ltac:(lia) Hle
    ltac:(eassumption) ltac:(eassumption) ltac:(lia) ltac:(lia)
    ltac:(eassumption)) as [Hrows Hptrs].
  assert (Hout_rows :
    out_size =
    Zlength (planet_between_rows_148 (planet_index_z_148 p1) (planet_index_z_148 p2))).
  {
    match goal with
    | Hsize : out_size = Zlength output_ptrs_2 |- _ => rewrite Hsize
    end.
    rewrite Hptrs.
    rewrite <- planet_between_rows_ptrs_Zlength_148.
    reflexivity.
  }
  rewrite Hout_rows.
  rewrite Hptrs.
  entailer!;
    try solve
      [ apply problem_148_spec_z_between_valid_148; assumption
      | apply planet_between_rows_ptrs_Zlength_148
      | apply planet_between_rows_Zlength_bound_148
      | rewrite Hout_rows; reflexivity
      | lia ].
Qed.








Lemma proof_of_bf_return_wit_2 : bf_return_wit_2.
Proof.
  right.
  pre_process_default.
  assert (Hbad : planet_index_z_148 p1 = -1).
  {
    eapply planet_scan_state_148_invalid; eauto; lia.
  }
  pose proof (planet_between_rows_invalid_left_148 p1 (planet_index_z_148 p2) Hbad)
    as [Hrows Hptrs].
  rewrite Hrows, Hptrs.
  simpl.
  sep_apply_l_atomic (PtrArray.undef_full_to_undef_seg data_2 6).
  rewrite PtrArray.seg_empty.
  entailer!;
    try solve
      [ apply problem_148_spec_z_invalid_left_148; exact Hbad
      | apply planet_between_rows_ptrs_Zlength_148
      | apply planet_between_rows_Zlength_bound_148
      | rewrite Zlength_nil; lia
      | lia ].
Qed.








Lemma proof_of_bf_return_wit_3 : bf_return_wit_3.
Proof.
  right.
  pre_process_default.
  assert (Hbad : planet_index_z_148 p2 = -1).
  {
    eapply planet_scan_state_148_invalid; eauto; lia.
  }
  pose proof (planet_between_rows_invalid_right_148 (planet_index_z_148 p1) p2 Hbad)
    as [Hrows Hptrs].
  rewrite Hrows, Hptrs.
  simpl.
  sep_apply_l_atomic (PtrArray.undef_full_to_undef_seg data_2 6).
  rewrite PtrArray.seg_empty.
  entailer!;
    try solve
      [ apply problem_148_spec_z_invalid_right_148; exact Hbad
      | apply planet_between_rows_ptrs_Zlength_148
      | apply planet_between_rows_Zlength_bound_148
      | rewrite Zlength_nil; lia
      | lia ].
Qed.

Ltac solve_bf_string_pure_148 :=
  left;
  pre_process_default;
  unfold planet_payloads_string_safe_148 in *;
  entailer!.

Lemma proof_of_bf_partial_solve_wit_3_pure : bf_partial_solve_wit_3_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_4_pure : bf_partial_solve_wit_4_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_5_pure : bf_partial_solve_wit_5_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_6_pure : bf_partial_solve_wit_6_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_7_pure : bf_partial_solve_wit_7_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_8_pure : bf_partial_solve_wit_8_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_9_pure : bf_partial_solve_wit_9_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_10_pure : bf_partial_solve_wit_10_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_11_pure : bf_partial_solve_wit_11_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_12_pure : bf_partial_solve_wit_12_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_13_pure : bf_partial_solve_wit_13_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_14_pure : bf_partial_solve_wit_14_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_15_pure : bf_partial_solve_wit_15_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_16_pure : bf_partial_solve_wit_16_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_17_pure : bf_partial_solve_wit_17_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_18_pure : bf_partial_solve_wit_18_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_19_pure : bf_partial_solve_wit_19_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_20_pure : bf_partial_solve_wit_20_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_21_pure : bf_partial_solve_wit_21_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_22_pure : bf_partial_solve_wit_22_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_23_pure : bf_partial_solve_wit_23_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_24_pure : bf_partial_solve_wit_24_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_25_pure : bf_partial_solve_wit_25_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_26_pure : bf_partial_solve_wit_26_pure.
Proof. solve_bf_string_pure_148. Qed.
