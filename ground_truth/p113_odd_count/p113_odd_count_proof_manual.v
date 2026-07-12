Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Numbers.DecimalString.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.ground_truth_p113_odd_count Require Import p113_odd_count_goal.
From SimpleC.EE.CAV.ground_truth_p113_odd_count Require Import p113_odd_count_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import p113_odd_count.
Local Open Scope sac.

(* BEGIN migrated companion-spec proofs *)
Module MigratedCompanionProofs.
Local Open Scope bool_scope.
Import ListNotations.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Import naive_C_Rules.
Local Open Scope sac.



Lemma count_odd_digits_payload_113_nonneg : forall s,
  0 <= count_odd_digits_payload_113 s.
Proof.
  induction s as [|c rest IH]; simpl.
  - lia.
  - destruct (is_odd_digit_z_113 c); lia.
Qed.

Lemma count_odd_digits_payload_113_le_Zlength : forall s,
  count_odd_digits_payload_113 s <= Zlength s.
Proof.
  induction s as [|c rest IH]; simpl.
  - rewrite Zlength_nil. lia.
  - rewrite Zlength_cons.
    destruct (is_odd_digit_z_113 c); lia.
Qed.

Lemma odd_digit_count_row_113_nonneg : forall row,
  0 <= odd_digit_count_row_113 row.
Proof.
  intros row.
  unfold odd_digit_count_row_113.
  apply count_odd_digits_payload_113_nonneg.
Qed.

Lemma odd_count_rows_heap_113_snoc : forall ptrs rows p row,
  Zlength ptrs = Zlength rows ->
  odd_count_rows_heap_113 ptrs rows **
  CharArray.full p (Zlength row) row |--
  odd_count_rows_heap_113 (ptrs ++ [p]) (rows ++ [row]).
Proof.
  induction ptrs as [|p0 ps IH]; intros rows p row Hlen.
  - destruct rows as [|r rs].
    + simpl. entailer!.
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
  - destruct rows as [|r rs].
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
    + simpl.
      assert (Htail : Zlength ps = Zlength rs).
      { rewrite !Zlength_correct in *. simpl in Hlen. lia. }
      sep_apply_l_atomic (IH rs p row Htail).
      cancel.
Qed.

Lemma template_len_113_value : template_len_113 = 56.
Proof.
  reflexivity.
Qed.

Lemma template_replace_Zlength_113 : forall digits,
  Zlength (replace_i_payload_113 template_payload_113 digits) =
  56 + 4 * (Zlength digits - 1).
Proof.
  intros digits.
  change (replace_i_payload_113 template_payload_113 digits) with
    ([116; 104; 101; 32; 110; 117; 109; 98; 101; 114; 32; 111; 102; 32;
      111; 100; 100; 32; 101; 108; 101; 109; 101; 110; 116; 115; 32] ++
     digits ++
     [110; 32; 116; 104; 101; 32; 115; 116; 114] ++
     digits ++
     [110; 103; 32] ++
     digits ++
     [32; 111; 102; 32; 116; 104; 101; 32] ++
     digits ++
     [110; 112; 117; 116; 46]).
  repeat rewrite Zlength_app.
  repeat rewrite Zlength_cons.
  repeat rewrite Zlength_nil.
  lia.
Qed.

Lemma odd_count_row_Zlength_113 : forall row,
  Zlength (odd_count_row_113 row) - 1 =
  56 + 4 * (Zlength (decimal_digits_113 (odd_digit_count_row_113 row)) - 1).
Proof.
  intros row.
  unfold odd_count_row_113, c_string, string_length.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  rewrite template_replace_Zlength_113.
  lia.
Qed.

Lemma uint_digits_z_113_in_range : forall d c,
  In c (uint_digits_z_113 d) ->
  48 <= c <= 57.
Proof.
  induction d; intros c Hin; simpl in Hin.
  - contradiction.
  - destruct Hin as [Hc | Hin]; [subst; lia|apply IHd; exact Hin].
  - destruct Hin as [Hc | Hin]; [subst; lia|apply IHd; exact Hin].
  - destruct Hin as [Hc | Hin]; [subst; lia|apply IHd; exact Hin].
  - destruct Hin as [Hc | Hin]; [subst; lia|apply IHd; exact Hin].
  - destruct Hin as [Hc | Hin]; [subst; lia|apply IHd; exact Hin].
  - destruct Hin as [Hc | Hin]; [subst; lia|apply IHd; exact Hin].
  - destruct Hin as [Hc | Hin]; [subst; lia|apply IHd; exact Hin].
  - destruct Hin as [Hc | Hin]; [subst; lia|apply IHd; exact Hin].
  - destruct Hin as [Hc | Hin]; [subst; lia|apply IHd; exact Hin].
  - destruct Hin as [Hc | Hin]; [subst; lia|apply IHd; exact Hin].
Qed.

Lemma decimal_digits_113_in_range : forall n c,
  0 <= n ->
  In c (decimal_digits_113 n) ->
  48 <= c <= 57.
Proof.
  intros n c _ Hin.
  unfold decimal_digits_113 in Hin.
  destruct (N.to_uint (N.of_nat (Z.to_nat n))) as
    [|u|u|u|u|u|u|u|u|u|u]; simpl in Hin.
  - destruct Hin as [Hc | Hin]; [subst; lia|contradiction].
  - apply (uint_digits_z_113_in_range (Decimal.D0 u)); simpl; exact Hin.
  - apply (uint_digits_z_113_in_range (Decimal.D1 u)); simpl; exact Hin.
  - apply (uint_digits_z_113_in_range (Decimal.D2 u)); simpl; exact Hin.
  - apply (uint_digits_z_113_in_range (Decimal.D3 u)); simpl; exact Hin.
  - apply (uint_digits_z_113_in_range (Decimal.D4 u)); simpl; exact Hin.
  - apply (uint_digits_z_113_in_range (Decimal.D5 u)); simpl; exact Hin.
  - apply (uint_digits_z_113_in_range (Decimal.D6 u)); simpl; exact Hin.
  - apply (uint_digits_z_113_in_range (Decimal.D7 u)); simpl; exact Hin.
  - apply (uint_digits_z_113_in_range (Decimal.D8 u)); simpl; exact Hin.
  - apply (uint_digits_z_113_in_range (Decimal.D9 u)); simpl; exact Hin.
Qed.

Lemma string_of_uint_digits_z_113 : forall d,
  string_of_list_z_113 (uint_digits_z_113 d) =
  NilEmpty.string_of_uint d.
Proof.
  induction d; simpl; try rewrite IHd; reflexivity.
Qed.

Lemma decimal_digits_string_113 : forall n,
  string_of_list_z_113 (decimal_digits_113 n) =
  nat_to_string (Z.to_nat n).
Proof.
  intros n.
  unfold decimal_digits_113, nat_to_string.
  destruct (N.to_uint (N.of_nat (Z.to_nat n))) eqn:Huint;
    simpl; try rewrite string_of_uint_digits_z_113; reflexivity.
Qed.

Lemma list_ascii_string_of_list_z_113 : forall l,
  list_ascii_of_string (string_of_list_z_113 l) = map ascii_of_z_113 l.
Proof.
  induction l; simpl; congruence.
Qed.

Lemma replace_i_payload_template_expanded_113 : forall digits,
  replace_i_payload_113 template_payload_113 digits =
  template_expanded_113 digits.
Proof.
  intros digits.
  reflexivity.
Qed.

Lemma map_template_expanded_113 : forall digits,
  map ascii_of_z_113 (template_expanded_113 digits) =
  template_expanded_ascii_113 digits.
Proof.
  intros digits.
  unfold template_expanded_113, template_expanded_ascii_113.
  repeat rewrite map_app.
  change (map ascii_of_z_113
    [116; 104; 101; 32; 110; 117; 109; 98; 101; 114; 32; 111; 102; 32;
     111; 100; 100; 32; 101; 108; 101; 109; 101; 110; 116; 115; 32])
    with (list_ascii_of_string "the number of odd elements ").
  change (map ascii_of_z_113
    [110; 32; 116; 104; 101; 32; 115; 116; 114])
    with (list_ascii_of_string "n the str").
  change (map ascii_of_z_113 [110; 103; 32])
    with (list_ascii_of_string "ng ").
  change (map ascii_of_z_113 [32; 111; 102; 32; 116; 104; 101; 32])
    with (list_ascii_of_string " of the ").
  change (map ascii_of_z_113 [110; 112; 117; 116; 46])
    with (list_ascii_of_string "nput.").
  reflexivity.
Qed.

Lemma template_replace_string_113 : forall digits,
  string_of_list_z_113
    (replace_i_payload_113 template_payload_113 digits) =
  replace_char_with_string
    "i"%char (string_of_list_z_113 digits) template_literal_113.
Proof.
  intros digits.
  rewrite <- (string_of_list_ascii_of_string
    (string_of_list_z_113 (replace_i_payload_113 template_payload_113 digits))).
  rewrite <- (string_of_list_ascii_of_string
    (replace_char_with_string
       "i"%char (string_of_list_z_113 digits) template_literal_113)).
  f_equal.
  rewrite list_ascii_string_of_list_z_113.
  rewrite replace_i_payload_template_expanded_113.
  rewrite map_template_expanded_113.
  unfold replace_char_with_string, template_literal_113.
  rewrite list_ascii_of_string_of_list_ascii.
  rewrite list_ascii_string_of_list_z_113.
  change (flat_map
    (fun c : ascii =>
       if Ascii.eqb c "i"%char
       then map ascii_of_z_113 digits
       else [c])
    (list_ascii_of_string
      "the number of odd elements in the string i of the input."%string))
    with (template_expanded_ascii_113 digits).
  reflexivity.
Qed.

Lemma is_odd_digit_ascii_of_z_113 : forall c,
  0 <= c <= 127 ->
  is_odd_digit (ascii_of_z_113 c) = is_odd_digit_z_113 c.
Proof.
  intros c Hc.
  Ltac solve_ascii_range c Hc lo hi :=
    lazymatch eval compute in (lo <=? hi)%Z with
    | true =>
        let lo' := eval compute in (lo + 1)%Z in
        destruct (Z.eq_dec c lo) as [->|];
        [ vm_compute; reflexivity | solve_ascii_range c Hc lo' hi ]
    | false => lia
    end.
  solve_ascii_range c Hc 0 127.
Qed.

Lemma all_ascii_cons_inv_113 : forall c rest,
  all_ascii (c :: rest) ->
  0 <= c <= 127 /\ all_ascii rest.
Proof.
  intros c rest Hascii.
  split.
  - specialize (Hascii 0).
    simpl in Hascii.
    apply Hascii.
    rewrite Zlength_cons.
    pose proof (Zlength_nonneg rest).
    lia.
  - intros i Hi.
    specialize (Hascii (i + 1)).
    simpl in Hascii.
    replace (Znth (i + 1) (c :: rest) 0) with (Znth i rest 0) in Hascii
      by (rewrite Znth_cons by lia; replace (i + 1 - 1) with i by lia; reflexivity).
    apply Hascii.
    rewrite Zlength_cons.
    pose proof (Zlength_nonneg rest).
    lia.
Qed.

Lemma count_odd_digits_string_of_list_z_113 : forall s,
  all_ascii s ->
  Z.of_nat (count_odd_digits (string_of_list_z_113 s)) =
  count_odd_digits_payload_113 s.
Proof.
  induction s as [|c rest IH]; intros Hascii.
  - reflexivity.
  - destruct (all_ascii_cons_inv_113 c rest Hascii) as [Hc Hrest].
    simpl.
    unfold count_odd_digits in *.
    simpl.
    rewrite is_odd_digit_ascii_of_z_113 by exact Hc.
    specialize (IH Hrest).
    unfold count_odd_digits in IH.
    simpl in IH.
    destruct (is_odd_digit_z_113 c).
    + change (Z.of_nat
        (S (Datatypes.length
          (filter is_odd_digit
            (list_ascii_of_string (string_of_list_z_113 rest))))) =
        1 + count_odd_digits_payload_113 rest).
      rewrite Nat2Z.inj_succ.
      lia.
    + change (Z.of_nat
        (Datatypes.length
          (filter is_odd_digit
            (list_ascii_of_string (string_of_list_z_113 rest)))) =
        count_odd_digits_payload_113 rest).
      exact IH.
Qed.

Lemma template_literal_payload_113 :
  StringToList template_literal_113 (StringLength template_literal_113 + 1) =
  template_payload_113 ++ [0].
Proof.
  reflexivity.
Qed.

Lemma template_literal_i_positions_113 : forall t,
  0 <= t < template_len_113 ->
  Znth t (StringToList template_literal_113 (StringLength template_literal_113 + 1)) 0 = 105 ->
  t = 27 \/ t = 37 \/ t = 41 \/ t = 50.
Proof.
  intros t Ht Hchar.
  rewrite template_len_113_value in Ht.
  unfold template_literal_113 in Hchar.
  Ltac solve_positions t Hchar lo hi :=
    lazymatch eval compute in (lo <=? hi)%Z with
    | true =>
        let lo' := eval compute in (lo + 1)%Z in
        destruct (Z.eq_dec t lo) as [->|];
        [ vm_compute in Hchar; lia | solve_positions t Hchar lo' hi ]
    | false => lia
    end.
  solve_positions t Hchar 0 55.
Qed.

Lemma template_prefix_len_27_113 : forall digits,
  Zlength (template_prefix_payload_113 27 digits) = 27.
Proof.
  intros digits.
  change (template_prefix_payload_113 27 digits) with
    [116; 104; 101; 32; 110; 117; 109; 98; 101; 114; 32; 111; 102; 32;
     111; 100; 100; 32; 101; 108; 101; 109; 101; 110; 116; 115; 32].
  repeat rewrite Zlength_cons.
  repeat rewrite Zlength_nil.
  lia.
Qed.

Lemma template_prefix_len_37_113 : forall digits,
  Zlength (template_prefix_payload_113 37 digits) = Zlength digits + 36.
Proof.
  intros digits.
  change (template_prefix_payload_113 37 digits) with
    ([116; 104; 101; 32; 110; 117; 109; 98; 101; 114; 32; 111; 102; 32;
      111; 100; 100; 32; 101; 108; 101; 109; 101; 110; 116; 115; 32] ++
     digits ++
     [110; 32; 116; 104; 101; 32; 115; 116; 114]).
  repeat rewrite Zlength_app.
  repeat rewrite Zlength_cons.
  repeat rewrite Zlength_nil.
  change (27 + (Zlength digits + 9) = Zlength digits + 36).
  lia.
Qed.

Lemma template_prefix_len_41_113 : forall digits,
  Zlength (template_prefix_payload_113 41 digits) =
  Zlength digits + Zlength digits + 39.
Proof.
  intros digits.
  change (template_prefix_payload_113 41 digits) with
    ([116; 104; 101; 32; 110; 117; 109; 98; 101; 114; 32; 111; 102; 32;
      111; 100; 100; 32; 101; 108; 101; 109; 101; 110; 116; 115; 32] ++
     digits ++
     [110; 32; 116; 104; 101; 32; 115; 116; 114] ++
     digits ++
     [110; 103; 32]).
  repeat rewrite Zlength_app.
  repeat rewrite Zlength_cons.
  repeat rewrite Zlength_nil.
  change (27 + (Zlength digits + (9 + (Zlength digits + 3))) =
          Zlength digits + Zlength digits + 39).
  lia.
Qed.

Lemma template_prefix_len_50_113 : forall digits,
  Zlength (template_prefix_payload_113 50 digits) =
  Zlength digits + Zlength digits + Zlength digits + 47.
Proof.
  intros digits.
  change (template_prefix_payload_113 50 digits) with
    ([116; 104; 101; 32; 110; 117; 109; 98; 101; 114; 32; 111; 102; 32;
      111; 100; 100; 32; 101; 108; 101; 109; 101; 110; 116; 115; 32] ++
     digits ++
     [110; 32; 116; 104; 101; 32; 115; 116; 114] ++
     digits ++
     [110; 103; 32] ++
     digits ++
     [32; 111; 102; 32; 116; 104; 101; 32]).
  repeat rewrite Zlength_app.
  repeat rewrite Zlength_cons.
  repeat rewrite Zlength_nil.
  change (27 + (Zlength digits + (9 + (Zlength digits + (3 +
          (Zlength digits + 8))))) =
          Zlength digits + Zlength digits + Zlength digits + 47).
  lia.
Qed.

Lemma replace_i_payload_app_113 : forall xs ys digits,
  replace_i_payload_113 (xs ++ ys) digits =
  replace_i_payload_113 xs digits ++ replace_i_payload_113 ys digits.
Proof.
  induction xs as [|c xs IH]; intros ys digits; simpl.
  - reflexivity.
  - destruct (Z.eqb c 105); simpl.
    + rewrite IH, app_assoc. reflexivity.
    + rewrite IH. reflexivity.
Qed.

Lemma template_firstn_i_step_27_113 :
  firstn (Z.to_nat 28) template_payload_113 =
  firstn (Z.to_nat 27) template_payload_113 ++ [105].
Proof. reflexivity. Qed.

Lemma template_firstn_i_step_37_113 :
  firstn (Z.to_nat 38) template_payload_113 =
  firstn (Z.to_nat 37) template_payload_113 ++ [105].
Proof. reflexivity. Qed.

Lemma template_firstn_i_step_41_113 :
  firstn (Z.to_nat 42) template_payload_113 =
  firstn (Z.to_nat 41) template_payload_113 ++ [105].
Proof. reflexivity. Qed.

Lemma template_firstn_i_step_50_113 :
  firstn (Z.to_nat 51) template_payload_113 =
  firstn (Z.to_nat 50) template_payload_113 ++ [105].
Proof. reflexivity. Qed.

Lemma template_prefix_i_step_27_113 : forall digits,
  template_prefix_payload_113 28 digits =
  template_prefix_payload_113 27 digits ++ digits.
Proof.
  intros digits.
  unfold template_prefix_payload_113.
  rewrite template_firstn_i_step_27_113.
  rewrite replace_i_payload_app_113.
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma template_prefix_i_step_37_113 : forall digits,
  template_prefix_payload_113 38 digits =
  template_prefix_payload_113 37 digits ++ digits.
Proof.
  intros digits.
  unfold template_prefix_payload_113.
  rewrite template_firstn_i_step_37_113.
  rewrite replace_i_payload_app_113.
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma template_prefix_i_step_41_113 : forall digits,
  template_prefix_payload_113 42 digits =
  template_prefix_payload_113 41 digits ++ digits.
Proof.
  intros digits.
  unfold template_prefix_payload_113.
  rewrite template_firstn_i_step_41_113.
  rewrite replace_i_payload_app_113.
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma template_prefix_i_step_50_113 : forall digits,
  template_prefix_payload_113 51 digits =
  template_prefix_payload_113 50 digits ++ digits.
Proof.
  intros digits.
  unfold template_prefix_payload_113.
  rewrite template_firstn_i_step_50_113.
  rewrite replace_i_payload_app_113.
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma template_literal_i_step_113 : forall t digits k out_l,
  template_fill_state_113 t digits k out_l ->
  0 <= t < template_len_113 ->
  Znth t (StringToList template_literal_113 (StringLength template_literal_113 + 1)) 0 = 105 ->
  template_fill_state_113 (t + 1) digits (k + Zlength digits) (out_l ++ digits).
Proof.
  intros t digits k out_l Hstate Ht Hchar.
  destruct Hstate as [Hrange [Hout Hk]].
  subst k out_l.
  pose proof (template_literal_i_positions_113 t Ht Hchar) as Hpos.
  destruct Hpos as [-> | [-> | [-> | ->]]].
  - unfold template_fill_state_113.
    rewrite template_prefix_i_step_27_113.
    repeat rewrite Zlength_app.
    rewrite template_prefix_len_27_113.
    split; [rewrite template_len_113_value; lia|].
    split; [reflexivity|lia].
  - unfold template_fill_state_113.
    rewrite template_prefix_i_step_37_113.
    repeat rewrite Zlength_app.
    rewrite template_prefix_len_37_113.
    split; [rewrite template_len_113_value; lia|].
    split; [reflexivity|lia].
  - unfold template_fill_state_113.
    rewrite template_prefix_i_step_41_113.
    repeat rewrite Zlength_app.
    rewrite template_prefix_len_41_113.
    split; [rewrite template_len_113_value; lia|].
    split; [reflexivity|lia].
  - unfold template_fill_state_113.
    rewrite template_prefix_i_step_50_113.
    repeat rewrite Zlength_app.
    rewrite template_prefix_len_50_113.
    split; [rewrite template_len_113_value; lia|].
    split; [reflexivity|lia].
Qed.

Lemma template_literal_i_room_113 : forall t digits k out_l,
  template_fill_state_113 t digits k out_l ->
  0 <= t < template_len_113 ->
  Znth t (StringToList template_literal_113 (StringLength template_literal_113 + 1)) 0 = 105 ->
  k + Zlength digits <= Zlength (replace_i_payload_113 template_payload_113 digits).
Proof.
  intros t digits k out_l Hstate Ht Hchar.
  destruct Hstate as [_ [Hout Hk]].
  subst k out_l.
  pose proof (template_literal_i_positions_113 t Ht Hchar) as Hpos.
  pose proof (template_replace_Zlength_113 digits) as Hfull.
  pose proof (Zlength_nonneg digits) as Hdigits_nonneg.
  destruct Hpos as [-> | [-> | [-> | ->]]].
  - rewrite template_prefix_len_27_113, Hfull. lia.
  - rewrite template_prefix_len_37_113, Hfull. lia.
  - rewrite template_prefix_len_41_113, Hfull. lia.
  - rewrite template_prefix_len_50_113, Hfull. lia.
Qed.

Lemma template_fill_state_complete_113 : forall t digits k out_l,
  template_fill_state_113 t digits k out_l ->
  t >= 56 ->
  t <= template_len_113 ->
  out_l = replace_i_payload_113 template_payload_113 digits /\
  k = Zlength (replace_i_payload_113 template_payload_113 digits).
Proof.
  intros t digits k out_l Hstate Hge Hle.
  destruct Hstate as [_ [Hout Hk]].
  assert (Ht : t = 56) by (rewrite template_len_113_value in Hle; lia).
  subst t.
  assert (Hprefix :
    template_prefix_payload_113 56 digits =
    replace_i_payload_113 template_payload_113 digits).
  {
    unfold template_prefix_payload_113.
    change (firstn (Z.to_nat 56) template_payload_113) with template_payload_113.
    reflexivity.
  }
  rewrite Hprefix in Hout.
  rewrite Hout in Hk.
  split; assumption.
Qed.

Lemma odd_count_row_complete_113 : forall row sum t k out_l,
  sum = odd_digit_count_row_113 row ->
  template_fill_state_113 t (decimal_digits_113 sum) k out_l ->
  t >= 56 ->
  t <= template_len_113 ->
  out_l ++ [0] = odd_count_row_113 row /\
  k + 1 = Zlength (odd_count_row_113 row).
Proof.
  intros row sum t k out_l Hsum Hstate Hge Hle.
  pose proof (template_fill_state_complete_113
                t (decimal_digits_113 sum) k out_l Hstate Hge Hle)
    as [Hout Hk].
  subst out_l k.
  rewrite Hsum.
  unfold odd_count_row_113, c_string, string_length.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  split; [reflexivity|lia].
Qed.

Lemma odd_count_state_113_initial : forall rows,
  odd_count_state_113 rows 0 nil.
Proof.
  intros rows.
  unfold odd_count_state_113, odd_count_rows_113.
  split; [rewrite Zlength_correct; lia|].
  reflexivity.
Qed.

Lemma sublist_0_firstn_113 : forall {A : Type} hi (l : list A),
  0 <= hi ->
  sublist 0 hi l = firstn (Z.to_nat hi) l.
Proof.
  intros A hi l _.
  unfold sublist.
  reflexivity.
Qed.

Lemma sublist_snoc_Znth_rows_113 : forall (l : list (list Z)) i,
  0 <= i < Zlength l ->
  sublist 0 (i + 1) l = sublist 0 i l ++ [Znth i l nil_z_113].
Proof.
  intros l i Hi.
  pose proof (@sublist_split (list Z) 0 (i + 1) i l ltac:(lia) ltac:(lia)) as Hsplit.
  rewrite Hsplit.
  replace (sublist i (i + 1) l) with [Znth i l nil_z_113].
  - reflexivity.
  - symmetry. apply sublist_single. lia.
Qed.

Lemma firstn_snoc_Znth_rows_113 : forall (l : list (list Z)) i,
  0 <= i < Zlength l ->
  firstn (Z.to_nat (i + 1)) l =
  firstn (Z.to_nat i) l ++ [Znth i l nil_z_113].
Proof.
  intros l i Hi.
  rewrite <- sublist_0_firstn_113 by lia.
  rewrite <- (sublist_0_firstn_113 i l) by lia.
  apply sublist_snoc_Znth_rows_113.
  exact Hi.
Qed.

Lemma odd_count_state_113_snoc : forall rows i output_rows,
  odd_count_state_113 rows i output_rows ->
  0 <= i < Zlength rows ->
  odd_count_state_113 rows (i + 1)
    (output_rows ++ [odd_count_row_113 (row_at_113 i rows)]).
Proof.
  intros rows i output_rows Hstate Hi.
  destruct Hstate as [Hrange Hrows].
  unfold odd_count_state_113, odd_count_rows_113 in *.
  split; [lia|].
  rewrite Hrows.
  rewrite firstn_snoc_Znth_rows_113 by exact Hi.
  rewrite map_app.
  simpl.
  unfold row_at_113, nil_z_113.
  reflexivity.
Qed.

Lemma odd_count_state_113_Zlength : forall rows i output_rows,
  odd_count_state_113 rows i output_rows ->
  Zlength output_rows = i.
Proof.
  intros rows i output_rows [Hrange Hrows].
  rewrite Hrows.
  unfold odd_count_rows_113.
  rewrite !Zlength_correct, length_map, length_firstn.
  rewrite Zlength_correct in Hrange.
  replace (Nat.min (Z.to_nat i) (Datatypes.length rows)) with (Z.to_nat i)
    by lia.
  lia.
Qed.

Lemma odd_count_rows_heap_113_nil :
  emp |-- odd_count_rows_heap_113 nil nil.
Proof.
  simpl.
  entailer!.
Qed.

Lemma rows_well_formed_113_row : forall rows n k,
  rows_well_formed_113 rows n ->
  0 <= k < n ->
  let row := Znth k rows nil in
  let payload := row_payload_z_113 row in
  row = c_string payload /\
  valid_string payload /\
  all_ascii payload /\
  string_length payload < INT_MAX /\
  Zlength row = string_length payload + 1.
Proof.
  intros rows n k [Hlen Hwf] Hk row payload.
  specialize (Hwf k Hk).
  destruct Hwf as [Hrow [Hvalid [Hascii Hlt]]].
  split; [exact Hrow|].
  split; [exact Hvalid|].
  split; [exact Hascii|].
  split; [exact Hlt|].
  subst row payload.
  rewrite Hrow at 1.
  unfold c_string, string_length.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma row_payload_c_string_113 : forall payload,
  row_payload_z_113 (c_string payload) = payload.
Proof.
  intros payload.
  unfold row_payload_z_113, c_string.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  rewrite Zlength_correct.
  replace (Z.of_nat (List.length payload) + Z.succ 0 - 1)
    with (Z.of_nat (List.length payload)) by lia.
  rewrite Nat2Z.id.
  replace (List.length payload) with (List.length payload + 0)%nat by lia.
  rewrite firstn_app_2.
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma row_string_odd_count_row_113 : forall row,
  all_ascii (row_payload_z_113 row) ->
  row_string_z_113 (odd_count_row_113 row) =
  process_string (row_string_z_113 row).
Proof.
  intros row Hascii.
  unfold row_string_z_113, odd_count_row_113.
  rewrite row_payload_c_string_113.
  unfold process_string.
  pose proof (count_odd_digits_string_of_list_z_113
                (row_payload_z_113 row) Hascii) as Hcount.
  replace (count_odd_digits (string_of_list_z_113 (row_payload_z_113 row)))
    with (Z.to_nat (odd_digit_count_row_113 row)).
  - rewrite template_replace_string_113.
    rewrite decimal_digits_string_113.
    reflexivity.
  - apply Nat2Z.inj.
    rewrite Z2Nat.id.
    + symmetry. exact Hcount.
    + apply odd_digit_count_row_113_nonneg.
Qed.

Lemma rows_well_formed_113_row_all_ascii : forall rows n k,
  rows_well_formed_113 rows n ->
  0 <= k < n ->
  all_ascii (row_payload_z_113 (Znth k rows nil)).
Proof.
  intros rows n k [_ Hwf] Hk.
  specialize (Hwf k Hk).
  simpl in Hwf.
  tauto.
Qed.

Lemma odd_count_rows_spec_113 : forall rows n,
  rows_well_formed_113 rows n ->
  problem_113_spec_z rows (odd_count_rows_113 rows).
Proof.
  induction rows as [|row rs IH]; intros n Hwf.
  unfold problem_113_spec_z, problem_113_spec, odd_count_impl.
  unfold rows_to_strings_z_113, odd_count_rows_113.
  rewrite !map_map.
  - reflexivity.
  - change
      (row_string_z_113 (odd_count_row_113 row) ::
       rows_to_strings_z_113 (odd_count_rows_113 rs) =
       process_string (row_string_z_113 row) ::
       odd_count_impl (rows_to_strings_z_113 rs)).
    f_equal.
    + apply row_string_odd_count_row_113.
      change row with (Znth 0 (row :: rs) nil).
      apply rows_well_formed_113_row_all_ascii with (n := n) (k := 0).
      * exact Hwf.
      * destruct Hwf as [Hlen _].
        rewrite <- Hlen.
        rewrite Zlength_cons.
        pose proof (Zlength_nonneg rs).
        lia.
    + apply IH with (n := n - 1).
      destruct Hwf as [Hlen Hrows].
      split.
      * rewrite Zlength_cons in Hlen.
        pose proof (Zlength_nonneg rs).
        lia.
      * intros k Hk.
        specialize (Hrows (k + 1)).
        assert (Hkrange : 0 <= k + 1 < n).
        { rewrite Zlength_cons in Hlen.
          pose proof (Zlength_nonneg rs).
          lia. }
        specialize (Hrows Hkrange).
        replace (Znth (k + 1) (row :: rs) nil) with (Znth k rs nil) in Hrows
          by (rewrite Znth_cons by lia; replace (k + 1 - 1) with k by lia; reflexivity).
        exact Hrows.
Qed.

Lemma c_string_Zlength_113 : forall payload,
  Zlength (c_string payload) = string_length payload + 1.
Proof.
  intros payload.
  unfold c_string, string_length.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma c_string_std_naive_113 : forall payload,
  string_lib.c_string payload = naive_C_Rules.c_string payload.
Proof.
  intros payload.
  reflexivity.
Qed.

Lemma row_payload_ascii_std_113 : forall rows n i j,
  rows_well_formed_113 rows n ->
  0 <= i < n ->
  0 <= j < string_length (row_payload_z_113 (row_at_113 i rows)) ->
  0 <= Znth j (string_lib.c_string (row_payload_z_113 (row_at_113 i rows))) 0 <= 127.
Proof.
  intros rows n i j Hwf Hi Hj.
  pose proof (rows_well_formed_113_row rows n i Hwf Hi) as Hrow.
  simpl in Hrow.
  destruct Hrow as [_ [_ [Hascii _]]].
  rewrite string_lib.c_string_Znth_inside by exact Hj.
  unfold all_ascii in Hascii.
  apply (Hascii j).
  change (0 <= j < string_length (row_payload_z_113 (row_at_113 i rows))).
  exact Hj.
Qed.

Lemma Znth_In_range_113 : forall (l : list Z) i d,
  0 <= i < Zlength l ->
  In (Znth i l d) l.
Proof.
  intros l i d Hi.
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hi.
  lia.
Qed.

Lemma decimal_digits_113_all_ascii : forall n,
  0 <= n ->
  all_ascii (decimal_digits_113 n).
Proof.
  intros n Hn i Hi.
  pose proof (Znth_In_range_113 (decimal_digits_113 n) i 0 Hi) as Hin.
  pose proof (decimal_digits_113_in_range n (Znth i (decimal_digits_113 n) 0) Hn Hin).
  lia.
Qed.

Lemma valid_string_std_113 : forall s,
  naive_C_Rules.valid_string s ->
  all_ascii s ->
  string_lib.valid_string s.
Proof.
  intros s Hvalid Hascii.
  unfold string_lib.valid_string, no_inner_nul.
  split; [exact Hascii|].
  intros i Hi.
  unfold naive_C_Rules.valid_string in Hvalid.
  rewrite Forall_forall in Hvalid.
  specialize (Hvalid (Znth i s 0) (Znth_In_range_113 s i 0 Hi)).
  unfold naive_C_Rules.valid_char in Hvalid.
  lia.
Qed.

Lemma odd_digit_count_prefix_113_zero : forall s,
  odd_digit_count_prefix_113 s 0 = 0.
Proof.
  intros s.
  unfold odd_digit_count_prefix_113.
  cbv [sublist].
  simpl.
  reflexivity.
Qed.

Lemma odd_digit_count_prefix_full_113 : forall s j,
  j = string_length s ->
  odd_digit_count_prefix_113 s j = count_odd_digits_payload_113 s.
Proof.
  intros s j Hj.
  unfold odd_digit_count_prefix_113.
  subst j.
  unfold string_length.
  rewrite (sublist_self s (Zlength s) eq_refl).
  reflexivity.
Qed.

Lemma sublist_snoc_Znth_113 : forall (l : list Z) i,
  0 <= i < Zlength l ->
  sublist 0 (i + 1) l = sublist 0 i l ++ [Znth i l 0].
Proof.
  intros l i Hi.
  pose proof (@sublist_split Z 0 (i + 1) i l ltac:(lia) ltac:(lia)) as Hsplit.
  rewrite Hsplit.
  replace (sublist i (i + 1) l) with [Znth i l 0].
  - reflexivity.
  - symmetry. apply sublist_single. lia.
Qed.

Lemma firstn_snoc_Znth_113 : forall (l : list Z) i,
  0 <= i < Zlength l ->
  firstn (Z.to_nat (i + 1)) l =
  firstn (Z.to_nat i) l ++ [Znth i l 0].
Proof.
  intros l i Hi.
  rewrite <- sublist_0_firstn_113 by lia.
  rewrite <- (sublist_0_firstn_113 i l) by lia.
  apply sublist_snoc_Znth_113.
  exact Hi.
Qed.

Lemma Znth_app_left_113 : forall (l1 l2 : list Z) i d,
  0 <= i < Zlength l1 ->
  Znth i (l1 ++ l2) d = Znth i l1 d.
Proof.
  intros l1 l2 i d Hi.
  unfold Znth.
  rewrite app_nth1.
  - reflexivity.
  - rewrite Zlength_correct in Hi.
    assert ((Z.to_nat i < Datatypes.length l1)%nat).
    { apply Nat2Z.inj_lt.
      rewrite Z2Nat.id by lia.
      lia. }
    lia.
Qed.

Lemma template_literal_char_payload_113 : forall t,
  0 <= t < template_len_113 ->
  Znth t (StringToList template_literal_113 (StringLength template_literal_113 + 1)) 0 =
  Znth t template_payload_113 0.
Proof.
  intros t Ht.
  rewrite template_literal_payload_113.
  apply Znth_app_left_113.
  rewrite template_len_113_value in Ht.
  unfold template_payload_113.
  repeat rewrite Zlength_cons.
  rewrite Zlength_nil.
  lia.
Qed.

Lemma template_payload_ascii_range_113 : forall c,
  In c template_payload_113 ->
  0 <= c <= 127.
Proof.
  intros c Hin.
  vm_compute in Hin.
  repeat (destruct Hin as [Hin | Hin]; [subst; lia|]).
  contradiction.
Qed.

Lemma template_literal_char_ascii_113 : forall t,
  0 <= t < template_len_113 ->
  0 <= Znth t (StringToList template_literal_113 (StringLength template_literal_113 + 1)) 0 <= 127.
Proof.
  intros t Ht.
  rewrite template_literal_char_payload_113 by exact Ht.
  apply template_payload_ascii_range_113.
  apply Znth_In_range_113.
  rewrite template_len_113_value in Ht.
  unfold template_payload_113.
  repeat rewrite Zlength_cons.
  rewrite Zlength_nil.
  lia.
Qed.

Lemma replace_i_payload_snoc_non_i_113 : forall xs c digits,
  c <> 105 ->
  replace_i_payload_113 (xs ++ [c]) digits =
  replace_i_payload_113 xs digits ++ [c].
Proof.
  intros xs c digits Hc.
  rewrite replace_i_payload_app_113.
  simpl.
  destruct (Z.eqb_spec c 105); [lia|].
  reflexivity.
Qed.

Lemma template_prefix_non_i_step_113 : forall t digits,
  0 <= t < template_len_113 ->
  Znth t (StringToList template_literal_113 (StringLength template_literal_113 + 1)) 0 <> 105 ->
  template_prefix_payload_113 (t + 1) digits =
  template_prefix_payload_113 t digits ++
  [Znth t (StringToList template_literal_113 (StringLength template_literal_113 + 1)) 0].
Proof.
  intros t digits Ht Hnon.
  unfold template_prefix_payload_113.
  rewrite (firstn_snoc_Znth_113 template_payload_113 t).
  - rewrite replace_i_payload_snoc_non_i_113.
    + rewrite template_literal_char_payload_113 by exact Ht.
      reflexivity.
    + rewrite <- template_literal_char_payload_113 by exact Ht.
      exact Hnon.
  - rewrite template_len_113_value in Ht.
    unfold template_payload_113.
    repeat rewrite Zlength_cons.
    rewrite Zlength_nil.
    lia.
Qed.

Lemma template_literal_non_i_step_113 : forall t digits k out_l,
  template_fill_state_113 t digits k out_l ->
  0 <= t < template_len_113 ->
  Znth t (StringToList template_literal_113 (StringLength template_literal_113 + 1)) 0 <> 105 ->
  template_fill_state_113 (t + 1) digits (k + 1)
    (out_l ++ [signed_last_nbits
       (Znth t (StringToList template_literal_113 (StringLength template_literal_113 + 1)) 0) 8]).
Proof.
  intros t digits k out_l Hstate Ht Hnon.
  pose proof (template_literal_char_ascii_113 t Ht) as Hascii.
  destruct Hstate as [Hrange [Hout Hk]].
  subst k out_l.
  rewrite (signed_last_nbits_eq
             (Znth t (StringToList template_literal_113 (StringLength template_literal_113 + 1)) 0) 8)
    by lia.
  unfold template_fill_state_113.
  rewrite template_prefix_non_i_step_113 by assumption.
  repeat rewrite Zlength_app.
  repeat rewrite Zlength_cons.
  repeat rewrite Zlength_nil.
  split; [lia|].
  split; [reflexivity|lia].
Qed.

Lemma replace_i_payload_firstn_bound_113 : forall l i digits,
  0 <= i <= Zlength l ->
  Zlength (replace_i_payload_113 (firstn (Z.to_nat i) l) digits) <=
  Zlength (replace_i_payload_113 l digits).
Proof.
  intros l i digits Hi.
  replace l with (firstn (Z.to_nat i) l ++ skipn (Z.to_nat i) l) at 2
    by (rewrite firstn_skipn; reflexivity).
  rewrite replace_i_payload_app_113.
  rewrite Zlength_app.
  pose proof (Zlength_nonneg (replace_i_payload_113 (firstn (Z.to_nat i) l) digits)).
  pose proof (Zlength_nonneg (replace_i_payload_113 (skipn (Z.to_nat i) l) digits)).
  lia.
Qed.

Lemma template_literal_non_i_room_113 : forall t digits k out_l,
  template_fill_state_113 t digits k out_l ->
  0 <= t < template_len_113 ->
  Znth t (StringToList template_literal_113 (StringLength template_literal_113 + 1)) 0 <> 105 ->
  k + 1 <= Zlength (replace_i_payload_113 template_payload_113 digits).
Proof.
  intros t digits k out_l Hstate Ht Hnon.
  destruct Hstate as [_ [Hout Hk]].
  subst k out_l.
  pose proof (template_prefix_non_i_step_113 t digits Ht Hnon) as Hstep.
  assert (Hnext_len :
    Zlength (template_prefix_payload_113 t digits) + 1 =
    Zlength (template_prefix_payload_113 (t + 1) digits)).
  {
    rewrite Hstep.
    rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  }
  rewrite Hnext_len.
  unfold template_prefix_payload_113.
  apply replace_i_payload_firstn_bound_113.
  rewrite template_len_113_value in Ht.
  unfold template_payload_113.
  repeat rewrite Zlength_cons.
  rewrite Zlength_nil.
  lia.
Qed.

Lemma count_odd_digits_payload_113_app_single : forall l c,
  count_odd_digits_payload_113 (l ++ [c]) =
  count_odd_digits_payload_113 l + (if is_odd_digit_z_113 c then 1 else 0).
Proof.
  induction l as [|x xs IH]; intros c; simpl.
  - lia.
  - rewrite IH. destruct (is_odd_digit_z_113 x); lia.
Qed.

Lemma is_odd_digit_z_113_true_mod : forall c,
  48 <= c <= 57 ->
  c mod 2 = 1 ->
  is_odd_digit_z_113 c = true.
Proof.
  intros c Hrange Hmod.
  assert (c = 48 \/ c = 49 \/ c = 50 \/ c = 51 \/ c = 52 \/
          c = 53 \/ c = 54 \/ c = 55 \/ c = 56 \/ c = 57) by lia.
  destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]];
    subst; cbv in Hmod |- *; try lia; reflexivity.
Qed.

Lemma is_odd_digit_z_113_false_lt : forall c,
  c < 48 ->
  is_odd_digit_z_113 c = false.
Proof.
  intros c Hlt.
  unfold is_odd_digit_z_113.
  repeat match goal with
  | |- context[Z.eqb c ?n] => destruct (Z.eqb_spec c n); [lia|]
  end.
  reflexivity.
Qed.

Lemma is_odd_digit_z_113_false_gt : forall c,
  57 < c ->
  is_odd_digit_z_113 c = false.
Proof.
  intros c Hgt.
  unfold is_odd_digit_z_113.
  repeat match goal with
  | |- context[Z.eqb c ?n] => destruct (Z.eqb_spec c n); [lia|]
  end.
  reflexivity.
Qed.

Lemma is_odd_digit_z_113_false_even_digit : forall c,
  48 <= c <= 57 ->
  c mod 2 <> 1 ->
  is_odd_digit_z_113 c = false.
Proof.
  intros c Hrange Hmod.
  assert (c = 48 \/ c = 49 \/ c = 50 \/ c = 51 \/ c = 52 \/
          c = 53 \/ c = 54 \/ c = 55 \/ c = 56 \/ c = 57) by lia.
  destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]];
    subst; cbv in Hmod |- *; try lia; reflexivity.
Qed.

Lemma odd_digit_count_prefix_step_113 : forall s j,
  0 <= j < string_length s ->
  odd_digit_count_prefix_113 s (j + 1) =
  odd_digit_count_prefix_113 s j +
  (if is_odd_digit_z_113 (Znth j (c_string s) 0) then 1 else 0).
Proof.
  intros s j Hj.
  unfold odd_digit_count_prefix_113.
  rewrite sublist_snoc_Znth_113 by (unfold string_length in Hj; lia).
  rewrite count_odd_digits_payload_113_app_single.
  rewrite c_string_Znth_inside by exact Hj.
  reflexivity.
Qed.
End MigratedCompanionProofs.
Export MigratedCompanionProofs.
(* END migrated companion-spec proofs *)

Lemma proof_of_odd_count_safety_wit_25 : odd_count_safety_wit_25.
Proof.
  left; intros; apply _derivable1_andp_intros; apply dump_spatial_left;
    pose proof (Zlength_nonneg (decimal_digits_113 sum)); lia.
Qed.

Lemma proof_of_odd_count_safety_wit_26 : odd_count_safety_wit_26.
Proof.
  left; intros; apply _derivable1_andp_intros; apply dump_spatial_left;
    pose proof (Zlength_nonneg (decimal_digits_113 sum)); lia.
Qed.

Lemma proof_of_odd_count_safety_wit_27 : odd_count_safety_wit_27.
Proof.
  left; intros; apply _derivable1_andp_intros; apply dump_spatial_left;
    pose proof (Zlength_nonneg (decimal_digits_113 sum)); lia.
Qed.

Lemma proof_of_odd_count_safety_wit_40 : odd_count_safety_wit_40.
Proof.
  left; intros; apply _derivable1_andp_intros; apply dump_spatial_left;
    pose proof template_len_113_value; lia.
Qed.

Lemma proof_of_odd_count_entail_wit_1 : odd_count_entail_wit_1.
Proof.
  constructor.
  - pre_process_default.
    intros.
    Exists (@nil Z) (@nil (list Z)).
    sep_apply_l_atomic (PtrArray.undef_full_to_undef_seg retval_2 lst_size_pre).
    rewrite PtrArray.seg_empty.
    sep_apply_l_atomic (GlobalStrings_split LitMap template_literal_113).
    unfold template_literal_113.
    entailer!.
    + simpl. rewrite Z.add_0_r. entailer!.
    + apply odd_count_state_113_initial.
    + pose proof template_len_113_value; lia.
Qed.

Lemma proof_of_odd_count_entail_wit_2 : odd_count_entail_wit_2.
Proof.
  constructor.
  - pre_process_default.
    pose proof (rows_well_formed_113_row rows lst_size_pre i PreH20 ltac:(lia))
      as Hrow.
    simpl in Hrow.
    destruct Hrow as [Hrow_eq [Hvalid [Hascii [Hstrlen Hlen]]]].
    sep_apply_l_atomic (CharPtrArray2.full_split_to_missing_i lst_pre i lst_size_pre rows).
    + dump_pre_spatial. lia.
    + Intros row_ptr.
      Exists output_ptrs_2 row_ptr output_rows_2.
      unfold StorePtrAsElement.storeA.
      rewrite sizeof_ptr.
      change (CharPtrArray2.ElemArray.full row_ptr (Zlength (Znth i rows nil)) (Znth i rows nil))
        with (CharArray.full row_ptr (Zlength (Znth i rows nil)) (Znth i rows nil)).
      unfold store_string.
      rewrite Hrow_eq.
      repeat rewrite row_payload_c_string_113.
      repeat rewrite c_string_Zlength_113.
      entailer!.
      apply valid_string_std_113; assumption.
Qed.

Lemma proof_of_odd_count_entail_wit_3 : odd_count_entail_wit_3.
Proof.
  constructor.
  - pre_process_default.
    Exists output_ptrs_2 output_rows_2.
    entailer!.
    + rewrite PreH1.
      apply string_length_nonneg.
Qed.

Lemma proof_of_odd_count_entail_wit_4_1 : odd_count_entail_wit_4_1.
Proof.
  constructor.
  - pre_process_default.
    Exists output_ptrs_2 output_rows_2.
    entailer!.
    rewrite PreH10.
    assert (Hj : 0 <= j <
      string_length (row_payload_z_113 (row_at_113 i rows))) by lia.
    try rewrite (odd_digit_count_prefix_step_113
                   (row_payload_z_113 (row_at_113 i rows)) j Hj).
    change (naive_C_Rules.c_string (row_payload_z_113 (row_at_113 i rows)))
      with (c_string (row_payload_z_113 (row_at_113 i rows))).
    assert (Hrange :
      48 <= Znth j (c_string (row_payload_z_113 (row_at_113 i rows))) 0 <= 57)
      by lia.
    assert (Hmod :
      Znth j (c_string (row_payload_z_113 (row_at_113 i rows))) 0 mod 2 = 1)
      by (rewrite <- Z.rem_mod_nonneg by lia; exact PreH1).
    pose proof (is_odd_digit_z_113_true_mod _ Hrange Hmod) as Hodd.
    try rewrite Hodd.
    entailer!.
Qed.

Lemma proof_of_odd_count_entail_wit_4_2 : odd_count_entail_wit_4_2.
Proof.
  constructor.
  - pre_process_default.
    Exists output_ptrs_2 output_rows_2.
    assert (Hj : 0 <= j <
      string_length (row_payload_z_113 (row_at_113 i rows))) by lia.
    entailer!.
    + apply (proj2 (row_payload_ascii_std_113 rows lst_size_pre i j PreH24 ltac:(lia) Hj)).
    + rewrite PreH9.
      rewrite (odd_digit_count_prefix_step_113
                 (row_payload_z_113 (row_at_113 i rows)) j Hj).
      change (naive_C_Rules.c_string (row_payload_z_113 (row_at_113 i rows)))
        with (c_string (row_payload_z_113 (row_at_113 i rows))).
      assert (Hgt :
        57 < Znth j (c_string (row_payload_z_113 (row_at_113 i rows))) 0)
        by lia.
      pose proof (is_odd_digit_z_113_false_gt _ Hgt) as Hnotodd.
      rewrite Hnotodd.
      lia.
Qed.

Lemma proof_of_odd_count_entail_wit_4_3 : odd_count_entail_wit_4_3.
Proof.
  constructor.
  - pre_process_default.
    Exists output_ptrs_2 output_rows_2.
    assert (Hj : 0 <= j <
      string_length (row_payload_z_113 (row_at_113 i rows))) by lia.
    entailer!.
    + apply (proj1 (row_payload_ascii_std_113 rows lst_size_pre i j PreH23 ltac:(lia) Hj)).
    + rewrite PreH8.
      rewrite (odd_digit_count_prefix_step_113
                 (row_payload_z_113 (row_at_113 i rows)) j Hj).
      change (naive_C_Rules.c_string (row_payload_z_113 (row_at_113 i rows)))
        with (c_string (row_payload_z_113 (row_at_113 i rows))).
      pose proof (is_odd_digit_z_113_false_lt _ PreH1) as Hnotodd.
      rewrite Hnotodd.
      lia.
Qed.

Lemma proof_of_odd_count_entail_wit_4_4 : odd_count_entail_wit_4_4.
Proof.
  constructor.
  - pre_process_default.
    Exists output_ptrs_2 output_rows_2.
    entailer!.
    try rewrite PreH10.
    assert (Hj : 0 <= j <
      string_length (row_payload_z_113 (row_at_113 i rows))) by lia.
    rewrite (odd_digit_count_prefix_step_113
               (row_payload_z_113 (row_at_113 i rows)) j Hj).
    change (naive_C_Rules.c_string (row_payload_z_113 (row_at_113 i rows)))
      with (c_string (row_payload_z_113 (row_at_113 i rows))).
    assert (Hrange :
      48 <= Znth j (c_string (row_payload_z_113 (row_at_113 i rows))) 0 <= 57)
      by lia.
    assert (Hmod :
      Znth j (c_string (row_payload_z_113 (row_at_113 i rows))) 0 mod 2 <> 1)
      by (rewrite <- Z.rem_mod_nonneg by lia; exact PreH1).
    pose proof (is_odd_digit_z_113_false_even_digit _ Hrange Hmod) as Hnotodd.
    try rewrite Hnotodd.
    entailer!.
Qed.

Lemma proof_of_odd_count_entail_wit_5 : odd_count_entail_wit_5.
Proof.
  constructor.
  - pre_process_default.
    pose proof (rows_well_formed_113_row rows lst_size_pre i PreH22 ltac:(lia))
      as Hrow.
    simpl in Hrow.
    destruct Hrow as [_ [_ [_ [Hstrlen _]]]].
    assert (Hsumrow : sum = odd_digit_count_row_113 (row_at_113 i rows)).
    {
      rewrite PreH7.
      unfold odd_digit_count_row_113.
      apply odd_digit_count_prefix_full_113.
      replace j with n by lia.
      exact PreH6.
    }
    Exists output_ptrs_2 output_rows_2.
    entailer!.
    + rewrite Hsumrow.
      apply PreH23.
      lia.
    + unfold row_at_113 in *.
      unfold nil_z_113 in *.
      unfold string_length, naive_C_Rules.string_length in *.
      lia.
Qed.

Lemma proof_of_odd_count_entail_wit_6 : odd_count_entail_wit_6.
Proof.
  constructor.
  - pre_process_default.
    assert (Houtlen_eq :
      56 + 4 * (retval - 1) =
      Zlength (odd_count_row_113 (row_at_113 i rows)) - 1).
    {
      rewrite odd_count_row_Zlength_113.
      rewrite <- PreH9.
      rewrite <- PreH4.
      lia.
    }
    assert (Houtlen_lt : 56 + 4 * (retval - 1) < INT_MAX).
    {
      pose proof (PreH27 i ltac:(lia)).
      lia.
    }
    Exists output_ptrs_2 output_rows_2 (@nil Z).
    sep_apply CharArray.undef_full_to_undef_seg.
    rewrite (CharArray.full_empty retval_2 0).
    entailer!.
    unfold template_fill_state_113.
    split.
    + rewrite template_len_113_value; lia.
    + split.
      * unfold template_prefix_payload_113; simpl; reflexivity.
      * rewrite Zlength_nil; lia.
Qed.

Lemma proof_of_odd_count_entail_wit_7 : odd_count_entail_wit_7.
Proof.
  constructor.
  - pre_process_default.
    assert (Hroom_bound : k + numlen <= outlen).
    {
      assert (Ht_range : 0 <= t < template_len_113).
      { rewrite template_len_113_value. lia. }
      pose proof (template_literal_i_room_113
                    t (decimal_digits_113 sum) k out_l_2
                    PreH13 Ht_range PreH1) as Hroom.
      assert (Houtlen_formula :
        outlen = 56 + 4 * (Zlength (decimal_digits_113 sum) - 1)).
      {
        rewrite PreH12.
        rewrite odd_count_row_Zlength_113.
        rewrite <- PreH8.
        lia.
      }
      rewrite template_replace_Zlength_113 in Hroom.
      rewrite PreH9.
      lia.
    }
    Exists output_ptrs_2 output_rows_2 out_l_2.
    sep_apply (CharArray.undef_seg_split_to_undef_seg row_out k (k + numlen) (outlen + 1)).
    2: { pose proof (Zlength_nonneg (decimal_digits_113 sum)); lia. }
    sep_apply (CharArray.undef_seg_to_undef_full row_out k (k + numlen)).
    replace (k + numlen - k) with numlen by lia.
    entailer!.
    apply decimal_digits_113_all_ascii.
    rewrite PreH8.
    apply odd_digit_count_row_113_nonneg.
Qed.

Lemma proof_of_odd_count_entail_wit_8_1 : odd_count_entail_wit_8_1.
Proof.
  constructor.
  - pre_process_default.
    Exists output_ptrs_2 output_rows_2 (out_l_2 ++ decimal_digits_113 sum).
    pose proof (Zlength_nonneg (decimal_digits_113 sum)) as Hnumlen_nonneg.
    replace numlen with (k + numlen - k) at 1 by lia.
    sep_apply_l_atomic (CharArray.full_merge_to_full
                          row_out k (k + numlen) out_l_2 (decimal_digits_113 sum)).
    + dump_pre_spatial. lia.
    + entailer!.
      rewrite PreH10.
      apply template_literal_i_step_113; try exact PreH15; try lia.
Qed.

Lemma proof_of_odd_count_entail_wit_8_2 : odd_count_entail_wit_8_2.
Proof.
  constructor.
  - pre_process_default.
    assert (Hroom_bound : k + 1 <= outlen).
    {
      assert (Ht_range : 0 <= t < template_len_113).
      { rewrite template_len_113_value. lia. }
      pose proof (template_literal_non_i_room_113
                    t (decimal_digits_113 sum) k out_l_2
                    PreH16 Ht_range PreH4) as Hroom.
      rewrite template_replace_Zlength_113 in Hroom.
      assert (Houtlen_formula :
        outlen = 56 + 4 * (Zlength (decimal_digits_113 sum) - 1)).
      {
        rewrite PreH15.
        rewrite odd_count_row_Zlength_113.
        rewrite <- PreH11.
        lia.
      }
      lia.
    }
    Exists output_ptrs_2 output_rows_2
      (out_l_2 ++
       cons (signed_last_nbits
         (Znth t (StringToList template_literal_113 (StringLength template_literal_113 + 1)) 0) 8) nil).
    entailer!.
    + pose proof (template_literal_char_ascii_113 t ltac:(rewrite template_len_113_value; lia)).
      lia.
    + pose proof (template_literal_char_ascii_113 t ltac:(rewrite template_len_113_value; lia)).
      lia.
    + apply template_literal_non_i_step_113; try exact PreH16; try lia.
      rewrite template_len_113_value; lia.
    + rewrite template_len_113_value; lia.
    all: try solve [
      pose proof (template_literal_char_ascii_113 t ltac:(rewrite template_len_113_value; lia));
      lia
    ].
    all: try solve [
      apply template_literal_non_i_step_113; try exact PreH16; try lia;
      rewrite template_len_113_value; lia
    ].
    all: try solve [rewrite template_len_113_value; lia].
Qed.

Lemma proof_of_odd_count_entail_wit_9 : odd_count_entail_wit_9.
Proof.
  constructor.
  - pre_process_default.
    pose proof (odd_count_row_complete_113
                  (row_at_113 i rows) sum t k out_l
                  PreH11 PreH16 PreH5 PreH7) as [Hrow Hrowlen].
    assert (Ht_eq : t = template_len_113).
    { pose proof template_len_113_value. lia. }
    assert (Hk_outlen : k = outlen).
    {
      rewrite PreH15.
      rewrite <- Hrowlen.
      lia.
    }
    prop_apply (PtrArray.seg_Zlength data 0 (i + 1) (output_ptrs_2 ++ row_out :: nil)).
    Intros_p Hseg_output_len.
    assert (Houtput_ptrs_len : Zlength output_ptrs_2 = i).
    {
      rewrite Zlength_app, Zlength_cons, Zlength_nil in Hseg_output_len.
      lia.
    }
    Exists (output_ptrs_2 ++ row_out :: nil)
           (output_rows_2 ++ odd_count_row_113 (row_at_113 i rows) :: nil).
    rewrite sizeof_ptr.
    pose proof (rows_well_formed_113_row rows lst_size_pre i PreH24 ltac:(lia))
      as Hinput_row.
    simpl in Hinput_row.
    destruct Hinput_row as [Hinput_eq [_ [_ [Hinput_lt Hinput_len]]]].
    assert (Hsum_lt : sum < INT_MAX).
    {
      rewrite PreH11.
      unfold odd_digit_count_row_113.
      pose proof (count_odd_digits_payload_113_le_Zlength
                    (row_payload_z_113 (row_at_113 i rows))) as Hcount_le.
      unfold row_at_113, nil_z_113 in Hcount_le |- *.
      change (naive_C_Rules.string_length (row_payload_z_113 (Znth i rows nil)))
        with (string_length (row_payload_z_113 (Znth i rows nil))) in Hinput_lt.
      unfold string_length in Hinput_lt.
      lia.
    }
    assert (Hsum_nonneg : 0 <= sum).
    {
      rewrite PreH11.
      apply odd_digit_count_row_113_nonneg.
    }
    assert (Hn_lt : n < INT_MAX).
    {
      rewrite PreH10.
      unfold row_at_113, nil_z_113 in Hinput_lt |- *.
      change (naive_C_Rules.string_length (row_payload_z_113 (Znth i rows nil)))
        with (string_length (row_payload_z_113 (Znth i rows nil))) in Hinput_lt.
      exact Hinput_lt.
    }
    assert (Hn_nonneg : 0 <= n).
    {
      rewrite PreH10.
      unfold string_length.
      apply Zlength_nonneg.
    }
    assert (Hnumlen_room : 0 <= numlen + 1 <= 32).
    {
      specialize (PreH25 i ltac:(lia)) as Hdigits_room.
      rewrite <- PreH11 in Hdigits_room.
      rewrite <- PreH12 in Hdigits_room.
      lia.
    }
    pose proof (CharPtrArray2.missing_i_merge_to_full
      lst_pre i lst_size_pre row_ptr rows
      (c_string (row_payload_z_113 (row_at_113 i rows)))) as Hmerge.
    unfold StorePtrAsElement.storeA in Hmerge.
    rewrite c_string_Zlength_113 in Hmerge.
    change (naive_C_Rules.string_length (row_payload_z_113 (row_at_113 i rows)))
      with (string_length (row_payload_z_113 (row_at_113 i rows))) in Hmerge.
    change (CharPtrArray2.ElemArray.full row_ptr
      (string_length (row_payload_z_113 (row_at_113 i rows)) + 1)
      (c_string (row_payload_z_113 (row_at_113 i rows))))
      with (CharArray.full row_ptr
        (string_length (row_payload_z_113 (row_at_113 i rows)) + 1)
        (c_string (row_payload_z_113 (row_at_113 i rows)))) in Hmerge.
    sep_lift_L
      ((((lst_pre + i * 4) # Ptr |-> row_ptr)) ::
       (CharArray.full row_ptr
          (string_length (row_payload_z_113 (row_at_113 i rows)) + 1)
          (c_string (row_payload_z_113 (row_at_113 i rows)))) ::
       (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows) :: nil).
    sep_apply Hmerge; try lia.
    assert (Hreplace_rows :
      replace_Znth i (c_string (row_payload_z_113 (row_at_113 i rows))) rows = rows).
    {
      unfold row_at_113, nil_z_113.
      change (c_string (row_payload_z_113 (Znth i rows nil)))
        with (naive_C_Rules.c_string (row_payload_z_113 (Znth i rows nil))).
      rewrite <- Hinput_eq.
      apply replace_Znth_Znth.
    }
    rewrite Hreplace_rows.
    unfold store_string.
    replace (out_l ++ 0 :: nil) with (odd_count_row_113 (row_at_113 i rows))
      by (symmetry; exact Hrow).
    replace (k + 1) with (Zlength (odd_count_row_113 (row_at_113 i rows)))
      by (symmetry; exact Hrowlen).
    replace (outlen + 1) with (Zlength (odd_count_row_113 (row_at_113 i rows))) by lia.
    rewrite (CharArray.undef_seg_empty row_out
      (Zlength (odd_count_row_113 (row_at_113 i rows)))).
    sep_apply (odd_count_rows_heap_113_snoc
                 output_ptrs_2 output_rows_2 row_out
                 (odd_count_row_113 (row_at_113 i rows))).
    sep_apply (CharArray.full_to_undef_full numbuf numlen (decimal_digits_113 sum)).
    sep_apply (CharArray.full_to_undef_full (numbuf + numlen * sizeof(CHAR)) 1 (0 :: nil)).
    replace 1 with (numlen + 1 - numlen) at 1 by lia.
    sep_lift_L
      ((CharArray.undef_full numbuf numlen) ::
       (CharArray.undef_full (numbuf + numlen * sizeof(CHAR)) (numlen + 1 - numlen)) :: nil).
    sep_apply (CharArray.undef_full_merge_to_undef_full numbuf numlen (numlen + 1)).
    sep_apply (CharArray.undef_full_to_undef_seg numbuf (numlen + 1)).
    replace (numbuf + 0 * sizeof(CHAR)) with numbuf by lia.
    replace (numlen + 1 - 0) with (numlen + 1) by lia.
    sep_apply (CharArray.undef_seg_merge_to_undef_full numbuf 0 (numlen + 1) 32).
    replace (numbuf + 0 * sizeof(CHAR)) with numbuf by lia.
    replace (32 - 0) with 32 by lia.
    cancel.
    entailer!.
    -- assert (Hrows_len_total : Zlength rows = lst_size_pre).
       { destruct PreH24 as [Hlen _]; exact Hlen. }
       apply odd_count_state_113_snoc; try exact PreH28.
       rewrite Hrows_len_total; lia.
    -- exact Hnumlen_room.
    -- split; [exact PreH4 | lia].
    -- rewrite Houtput_ptrs_len.
       symmetry.
       apply odd_count_state_113_Zlength with (rows := rows).
       exact PreH28.
Qed.

Lemma proof_of_odd_count_return_wit_1 : odd_count_return_wit_1.
Proof.
  constructor.
  pre_process_default.
  assert (Hi_eq : i = lst_size_pre) by lia.
  subst i.
  assert (Houtput_rows_eq : output_rows_2 = odd_count_rows_113 rows).
  {
    destruct PreH24 as [_ Hrows_state].
    unfold odd_count_rows_113 in Hrows_state |- *.
    rewrite firstn_all2 in Hrows_state.
    - exact Hrows_state.
    - destruct PreH20 as [Hlen _].
      rewrite Zlength_correct in Hlen.
      lia.
  }
  Exists numbuf output_ptrs_2 (odd_count_rows_113 rows) data_2.
  rewrite Hi_eq.
  rewrite (PtrArray.undef_seg_empty data_2 lst_size_pre).
  rewrite Houtput_rows_eq.
  rewrite PreH26.
  sep_apply (GlobalStrings_merge LitMap template_literal_113).
  entailer!.
  - apply odd_count_rows_spec_113 with (n := lst_size_pre).
    exact PreH20.
  - rewrite <- Houtput_rows_eq.
    rewrite <- Hi_eq.
    apply odd_count_state_113_Zlength with (rows := rows).
    exact PreH24.
Qed.
