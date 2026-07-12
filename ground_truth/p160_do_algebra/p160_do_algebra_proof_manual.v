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
