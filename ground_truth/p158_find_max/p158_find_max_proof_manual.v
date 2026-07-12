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
From SimpleC.EE.CAV.ground_truth_p158_find_max Require Import p158_find_max_goal.
From SimpleC.EE.CAV.ground_truth_p158_find_max Require Import p158_find_max_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import p158_find_max.
Local Open Scope sac.

(* BEGIN migrated companion-spec proofs *)
Module MigratedCompanionProofs.
Local Open Scope bool_scope.
Import ListNotations.
Import ListNotations.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope sac.



Lemma rows_well_formed_158_row : forall rows n k,
  rows_well_formed_158 rows n ->
  0 <= k < n ->
  let row := Znth k rows nil in
  let payload := row_payload_z_158 row in
  row = string_lib.c_string payload /\
  string_lib.valid_string payload /\
  string_lib.string_length payload < INT_MAX /\
  (forall j,
     0 <= j <= string_lib.string_length payload ->
     Z.of_nat
       (count_unique_chars
          (string_of_list_z_158 (firstn (Z.to_nat j) payload))) <= 128) /\
  row_unique_count_z_158 row <= 128 /\
  Zlength row = string_lib.string_length payload + 1.
Proof.
  intros rows n k [Hlen Hwf] Hk row payload.
  specialize (Hwf k Hk).
  destruct Hwf as [Hrow [Hvalid [Hlt [Hprefix Hbound]]]].
  split; [exact Hrow|].
  split; [exact Hvalid|].
  split; [exact Hlt|].
  split; [exact Hprefix|].
  split; [exact Hbound|].
  subst row payload.
  rewrite Hrow at 1.
  unfold string_lib.c_string, string_lib.string_length.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma row_payload_c_string_158 : forall payload,
  row_payload_z_158 (string_lib.c_string payload) = payload.
Proof.
  intros payload.
  unfold row_payload_z_158, string_lib.c_string.
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

Lemma c_string_Zlength_158 : forall payload,
  Zlength (string_lib.c_string payload) = string_lib.string_length payload + 1.
Proof.
  intros payload.
  unfold string_lib.c_string, string_lib.string_length.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma rows_well_formed_158_char_bound : forall rows n i j,
  rows_well_formed_158 rows n ->
  0 <= i < n ->
  0 <= j < string_lib.string_length (row_payload_z_158 (Znth i rows nil)) ->
  0 <= Znth j (Znth i rows nil) 0 <= 127.
Proof.
  intros rows n i j Hwf Hi Hj.
  pose proof (rows_well_formed_158_row rows n i Hwf Hi) as Hrow_info.
  destruct Hrow_info as [Hrow [Hvalid [_ [_ [_ _]]]]].
  rewrite Hrow.
  rewrite string_lib.c_string_Znth_inside by exact Hj.
  destruct Hvalid as [Hascii _].
  apply Hascii.
  unfold string_lib.string_length in Hj.
  lia.
Qed.

Lemma firstn_succ_Znth_158 : forall {A : Type} (l : list A) i d,
  0 <= i < Zlength l ->
  firstn (Z.to_nat (i + 1)) l =
  List.app (firstn (Z.to_nat i) l) [Znth i l d].
Proof.
  intros A l.
  assert (Hnat: forall n (xs : list A) d,
    (n < List.length xs)%nat ->
    firstn (S n) xs = List.app (firstn n xs) [nth n xs d]).
  {
    induction n as [|n IH]; intros xs d Hn.
    - destruct xs as [|x xs]; simpl in *; [lia|reflexivity].
    - destruct xs as [|x xs]; simpl in *; [lia|].
      rewrite (IH xs d) by lia. reflexivity.
  }
  intros i d Hi.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite (Hnat (Z.to_nat i) l d) by (rewrite Zlength_correct in Hi; lia).
  reflexivity.
Qed.

Lemma string_of_list_z_158_app : forall l1 l2,
  string_of_list_z_158 (l1 ++ l2) =
  String.append (string_of_list_z_158 l1) (string_of_list_z_158 l2).
Proof.
  induction l1 as [|x xs IH]; intros l2; simpl; auto.
  rewrite IH. reflexivity.
Qed.

Lemma string_contains_snoc_other_158 : forall s a c,
  a <> c ->
  string_contains a (String.append s (String c EmptyString)) =
  string_contains a s.
Proof.
  induction s as [|x xs IH]; intros a c Hneq; simpl.
  - destruct (Ascii.eqb a c) eqn:Heq; auto.
    apply Ascii.eqb_eq in Heq. contradiction.
  - destruct (Ascii.eqb a x); auto.
Qed.

Lemma count_unique_chars_snoc_new_158 : forall s c,
  string_contains c s = false ->
  count_unique_chars (String.append s (String c EmptyString)) =
  S (count_unique_chars s).
Proof.
  induction s as [|a s IH]; intros c Hnot; simpl in *.
  - reflexivity.
  - destruct (Ascii.eqb c a) eqn:Hca; [discriminate|].
    simpl.
    rewrite string_contains_snoc_other_158.
    + destruct (string_contains a s) eqn:Has.
      * apply IH. exact Hnot.
      * rewrite IH by exact Hnot. reflexivity.
    + intro Heq. subst.
      rewrite Ascii.eqb_refl in Hca. discriminate.
Qed.

Lemma string_contains_snoc_self_158 : forall s c,
  string_contains c (String.append s (String c EmptyString)) = true.
Proof.
  induction s as [|a s IH]; intros c; simpl.
  - rewrite Ascii.eqb_refl. reflexivity.
  - destruct (Ascii.eqb c a); auto.
Qed.

Lemma count_unique_chars_snoc_seen_158 : forall s c,
  string_contains c s = true ->
  count_unique_chars (String.append s (String c EmptyString)) =
  count_unique_chars s.
Proof.
  induction s as [|a s IH]; intros c Hseen; simpl in *.
  - discriminate.
  - destruct (Ascii.eqb c a) eqn:Hca.
    + apply Ascii.eqb_eq in Hca. subst c. simpl.
      rewrite string_contains_snoc_self_158.
      destruct (string_contains a s) eqn:Has.
      * apply IH. exact Has.
      * apply count_unique_chars_snoc_new_158. exact Has.
    + simpl.
      rewrite string_contains_snoc_other_158.
      * destruct (string_contains a s) eqn:Has.
        -- apply IH. exact Hseen.
        -- rewrite IH by exact Hseen. reflexivity.
      * intro Heq. subst.
        rewrite Ascii.eqb_refl in Hca. discriminate.
Qed.

Lemma string_contains_string_of_list_z_158_true_at : forall l p c,
  0 <= p < Zlength l ->
  c = Znth p l 0 ->
  string_contains (ascii_of_z_158 c) (string_of_list_z_158 l) = true.
Proof.
  induction l as [|x xs IH]; intros p c Hp Hc; simpl in *.
  - rewrite Zlength_nil in Hp. lia.
  - destruct (Z.eq_dec p 0) as [->|Hp0].
    + unfold Znth in Hc. simpl in Hc. subst c.
      rewrite Ascii.eqb_refl. reflexivity.
    + assert (0 <= p - 1 < Zlength xs).
      { rewrite Zlength_cons in Hp. lia. }
      assert (Hc_tail : c = Znth (p - 1) xs 0).
      { unfold Znth in *.
        replace (Z.to_nat p) with (S (Z.to_nat (p - 1))) in Hc by lia.
        simpl in Hc. exact Hc. }
      destruct (Ascii.eqb (ascii_of_z_158 c) (ascii_of_z_158 x)); auto.
      apply IH with (p := p - 1); auto.
Qed.

Lemma ascii_of_z_158_inj_128 : forall x y,
  0 <= x < 128 ->
  0 <= y < 128 ->
  ascii_of_z_158 x = ascii_of_z_158 y ->
  x = y.
Proof.
  intros x y Hx Hy Heq.
  unfold ascii_of_z_158 in Heq.
  apply f_equal with (f := nat_of_ascii) in Heq.
  rewrite !nat_ascii_embedding in Heq by lia.
  lia.
Qed.

Lemma all_ascii_firstn_158 : forall l n,
  string_lib.all_ascii l ->
  string_lib.all_ascii (firstn n l).
Proof.
  intros l n Hall i Hi.
  assert (Hi_l : 0 <= i < Zlength l).
  { rewrite Zlength_correct in *.
    rewrite length_firstn in Hi.
    lia. }
  assert (Hi_n : (Z.to_nat i < n)%nat).
  { rewrite Zlength_correct in Hi.
    rewrite length_firstn in Hi.
    lia. }
  specialize (Hall i Hi_l).
  unfold Znth.
  rewrite nth_firstn by exact Hi_n.
  unfold Znth in Hall.
  exact Hall.
Qed.

Lemma string_contains_string_of_list_z_158_false : forall l c,
  string_lib.all_ascii l ->
  0 <= c < 128 ->
  (forall p, 0 <= p < Zlength l -> Znth p l 0 <> c) ->
  string_contains (ascii_of_z_158 c) (string_of_list_z_158 l) = false.
Proof.
  induction l as [|x xs IH]; intros c Hall Hc Hnot; simpl.
  - reflexivity.
  - assert (Hx_bound : 0 <= x < 128).
    { assert (H0 : 0 <= 0 < Zlength (x :: xs)).
      { rewrite Zlength_cons. pose proof (Zlength_nonneg xs). lia. }
      specialize (Hall 0 H0).
      unfold Znth in Hall. simpl in Hall. lia. }
    destruct (Ascii.eqb (ascii_of_z_158 c) (ascii_of_z_158 x)) eqn:Heq.
    + apply Ascii.eqb_eq in Heq.
      apply ascii_of_z_158_inj_128 in Heq; try lia.
      subst x.
      assert (H0' : 0 <= 0 < Zlength (c :: xs)).
      { rewrite Zlength_cons. pose proof (Zlength_nonneg xs). lia. }
      specialize (Hnot 0 H0').
      unfold Znth in Hnot. simpl in Hnot. contradiction.
    + apply IH.
      * intros i Hi.
        assert (Hi_cons : 0 <= i + 1 < Zlength (x :: xs)).
        { rewrite Zlength_cons. lia. }
        specialize (Hall (i + 1) Hi_cons).
        unfold Znth in *.
        replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) in Hall by lia.
        simpl in Hall. exact Hall.
      * exact Hc.
      * intros p Hp Heqp.
        apply (Hnot (p + 1)).
        -- rewrite Zlength_cons. lia.
        -- unfold Znth in *.
           replace (Z.to_nat (p + 1)) with (S (Z.to_nat p)) by lia.
           simpl. exact Heqp.
Qed.

Lemma nth_remove_nth_before_158 : forall (A : Type) (n m : nat) (l : list A) d,
  (m < n)%nat ->
  (n < List.length l)%nat ->
  nth m ((firstn n l ++ skipn (S n) l)%list) d = nth m l d.
Proof.
  intros A n m l d Hmn Hn.
  rewrite app_nth1 by (rewrite length_firstn; lia).
  rewrite nth_firstn.
  destruct (Nat.ltb_spec m n); [reflexivity | lia].
  all: lia.
Qed.

Lemma nth_remove_nth_after_158 : forall (A : Type) (n m : nat) (l : list A) d,
  (n < m)%nat ->
  (m < List.length l)%nat ->
  nth (m - 1) ((firstn n l ++ skipn (S n) l)%list) d = nth m l d.
Proof.
  intros A n m l d Hnm Hm.
  rewrite app_nth2 by (rewrite length_firstn; lia).
  rewrite length_firstn.
  replace (m - 1 - Nat.min n (List.length l))%nat with (m - S n)%nat by lia.
  rewrite nth_skipn.
  replace (S n + (m - S n))%nat with m by lia.
  reflexivity.
Qed.

Lemma Znth_remove_Znth_before_158 : forall (A : Type) (i j : Z) (l : list A) d,
  0 <= j < i ->
  i < Zlength l ->
  Znth j (CharPtrArray2.remove_Znth i l) d = Znth j l d.
Proof.
  intros A i j l d Hji Hil.
  unfold CharPtrArray2.remove_Znth, Znth.
  apply nth_remove_nth_before_158.
  - lia.
  - rewrite Zlength_correct in Hil.
    lia.
Qed.

Lemma Znth_remove_Znth_after_158 : forall (A : Type) (i j : Z) (l : list A) d,
  0 <= i < j ->
  j < Zlength l ->
  Znth (j - 1) (CharPtrArray2.remove_Znth i l) d = Znth j l d.
Proof.
  intros A i j l d Hij Hjl.
  unfold CharPtrArray2.remove_Znth, Znth.
  replace (Z.to_nat (j - 1)) with (Z.to_nat j - 1)%nat by lia.
  apply nth_remove_nth_after_158.
  - lia.
  - rewrite Zlength_correct in Hjl.
    lia.
Qed.

Lemma Zlength_remove_Znth_158 : forall (A : Type) (i : Z) (l : list A),
  0 <= i < Zlength l ->
  Zlength (CharPtrArray2.remove_Znth i l) = Zlength l - 1.
Proof.
  intros A i l Hi.
  unfold CharPtrArray2.remove_Znth.
  rewrite !Zlength_correct.
  assert (Hi_nat : (Z.to_nat i < List.length l)%nat).
  { rewrite Zlength_correct in Hi. lia. }
  rewrite app_length, firstn_length, skipn_length.
  rewrite Nat.min_l by lia.
  replace (List.length l - S (Z.to_nat i))%nat
    with (List.length l - Z.to_nat i - 1)%nat by lia.
  lia.
Qed.

Lemma row_blocks_missing_i_split_other_158 :
  forall i j row_ptrs rows,
  Zlength row_ptrs = Zlength rows ->
  0 <= i < Zlength rows ->
  0 <= j < Zlength rows ->
  i <> j ->
  CharPtrArray2.row_blocks_missing_i i row_ptrs rows |--
    CharArray.full (Znth j row_ptrs 0) (Zlength (Znth j rows nil)) (Znth j rows nil) **
    row_blocks_except_two_158 i j row_ptrs rows.
Proof.
  intros i j row_ptrs rows Hlen Hij Hjj Hneq.
  unfold CharPtrArray2.row_blocks_missing_i, row_blocks_except_two_158.
  destruct (Z.ltb_spec i j) as [Hij_lt | Hij_ge].
  - assert (Hidx : 0 <= j - 1 <
        Zlength (CharPtrArray2.remove_Znth i (combine row_ptrs rows))).
    {
      rewrite Zlength_remove_Znth_158.
      - rewrite CharPtrArray2.Zlength_combine_eq by auto. lia.
      - rewrite CharPtrArray2.Zlength_combine_eq by auto. lia.
    }
    assert (Hznth :
      Znth (j - 1)
        (CharPtrArray2.remove_Znth i (combine row_ptrs rows)) (0, nil) =
      (Znth j row_ptrs 0, Znth j rows nil)).
    {
      rewrite (Znth_remove_Znth_after_158
        (Z * list Z)%type i j (combine row_ptrs rows) (0, nil))
        by (try rewrite CharPtrArray2.Zlength_combine_eq by auto; lia).
      rewrite CharPtrArray2.Znth_combine by (auto; lia).
      reflexivity.
    }
    sep_apply
      (CharPtrArray2.iter_sepcon_split_remove_Znth
        CharPtrArray2.row_block (j - 1)
        (CharPtrArray2.remove_Znth i (combine row_ptrs rows)) (0, nil) Hidx).
    unfold CharPtrArray2.row_block at 1.
    assert (Hfst :
      fst (Znth (j - 1)
        (CharPtrArray2.remove_Znth i (combine row_ptrs rows)) (0, nil)) =
      Znth j row_ptrs 0).
    {
      rewrite (Znth_remove_Znth_after_158
        (Z * list Z)%type i j (combine row_ptrs rows) (0, nil))
        by (try rewrite CharPtrArray2.Zlength_combine_eq by auto; lia).
      rewrite CharPtrArray2.Znth_combine by (auto; lia).
      reflexivity.
    }
    assert (Hsnd :
      snd (Znth (j - 1)
        (CharPtrArray2.remove_Znth i (combine row_ptrs rows)) (0, nil)) =
      Znth j rows nil).
    {
      rewrite (Znth_remove_Znth_after_158
        (Z * list Z)%type i j (combine row_ptrs rows) (0, nil))
        by (try rewrite CharPtrArray2.Zlength_combine_eq by auto; lia).
      rewrite CharPtrArray2.Znth_combine by (auto; lia).
      reflexivity.
    }
    setoid_rewrite Hfst.
    setoid_rewrite Hsnd.
    simpl.
    change (CharPtrArray2.ElemArray.full
      (Znth j row_ptrs 0) (Zlength (Znth j rows nil)) (Znth j rows nil))
      with (CharArray.full
        (Znth j row_ptrs 0) (Zlength (Znth j rows nil)) (Znth j rows nil)).
    entailer!.
  - assert (Hji : j < i) by lia.
    assert (Hidx : 0 <= j <
        Zlength (CharPtrArray2.remove_Znth i (combine row_ptrs rows))).
    {
      rewrite Zlength_remove_Znth_158.
      - rewrite CharPtrArray2.Zlength_combine_eq by auto. lia.
      - rewrite CharPtrArray2.Zlength_combine_eq by auto. lia.
    }
    assert (Hznth :
      Znth j
        (CharPtrArray2.remove_Znth i (combine row_ptrs rows)) (0, nil) =
      (Znth j row_ptrs 0, Znth j rows nil)).
    {
      rewrite (Znth_remove_Znth_before_158
        (Z * list Z)%type i j (combine row_ptrs rows) (0, nil))
        by (try rewrite CharPtrArray2.Zlength_combine_eq by auto; lia).
      rewrite CharPtrArray2.Znth_combine by (auto; lia).
      reflexivity.
    }
    sep_apply
      (CharPtrArray2.iter_sepcon_split_remove_Znth
        CharPtrArray2.row_block j
        (CharPtrArray2.remove_Znth i (combine row_ptrs rows)) (0, nil) Hidx).
    unfold CharPtrArray2.row_block at 1.
    assert (Hfst :
      fst (Znth j
        (CharPtrArray2.remove_Znth i (combine row_ptrs rows)) (0, nil)) =
      Znth j row_ptrs 0).
    {
      rewrite (Znth_remove_Znth_before_158
        (Z * list Z)%type i j (combine row_ptrs rows) (0, nil))
        by (try rewrite CharPtrArray2.Zlength_combine_eq by auto; lia).
      rewrite CharPtrArray2.Znth_combine by (auto; lia).
      reflexivity.
    }
    assert (Hsnd :
      snd (Znth j
        (CharPtrArray2.remove_Znth i (combine row_ptrs rows)) (0, nil)) =
      Znth j rows nil).
    {
      rewrite (Znth_remove_Znth_before_158
        (Z * list Z)%type i j (combine row_ptrs rows) (0, nil))
        by (try rewrite CharPtrArray2.Zlength_combine_eq by auto; lia).
      rewrite CharPtrArray2.Znth_combine by (auto; lia).
      reflexivity.
    }
    setoid_rewrite Hfst.
    setoid_rewrite Hsnd.
    simpl.
    change (CharPtrArray2.ElemArray.full
      (Znth j row_ptrs 0) (Zlength (Znth j rows nil)) (Znth j rows nil))
      with (CharArray.full
        (Znth j row_ptrs 0) (Zlength (Znth j rows nil)) (Znth j rows nil)).
    entailer!.
Qed.

Lemma char_ptr_array2_missing_i_split_two_158 :
  forall x n i j row_i rows,
  0 <= i < n ->
  0 <= j < n ->
  i <> j ->
  ((x + i * sizeof(PTR)) # Ptr |-> row_i) **
  CharArray.full row_i (Zlength (Znth i rows nil)) (Znth i rows nil) **
  CharPtrArray2.missing_i x n i row_i rows |--
  EX row_j,
    char_ptr_array2_missing_two_158 x n i row_i j row_j rows **
    ((x + j * sizeof(PTR)) # Ptr |-> row_j) **
    CharArray.full row_j (Zlength (Znth j rows nil)) (Znth j rows nil) **
    CharArray.full row_i (Zlength (Znth i rows nil)) (Znth i rows nil).
Proof.
  intros x n i j row_i rows Hi Hj Hneq.
  unfold CharPtrArray2.missing_i.
  Intros row_ptrs.
  destruct H as [Hrow_ptrs [Hrows Hrow_i]].
  subst row_i.
  assert (Hlen : Zlength row_ptrs = Zlength rows) by lia.
  eapply derivable1_trans with
    (y := ((((x + i * sizeof(PTR)) # Ptr |-> Znth i row_ptrs 0) **
            PtrArray.missing_i x i 0 n row_ptrs) **
           (CharPtrArray2.row_blocks_missing_i i row_ptrs rows **
            CharArray.full (Znth i row_ptrs 0)
              (Zlength (Znth i rows nil)) (Znth i rows nil)))).
  { entailer!. }
  pose proof (PtrArray.missing_i_merge_to_full
    x i n (Znth i row_ptrs 0) row_ptrs Hi) as Hptr_merge.
  unfold StorePtrAsElement.storeA in Hptr_merge.
  rewrite <- sizeof_ptr in Hptr_merge.
  sep_apply Hptr_merge.
  rewrite replace_Znth_Znth by lia.
  pose proof (PtrArray.full_split_to_missing_i x j n row_ptrs 0 Hj)
    as Hptr_split.
  unfold StorePtrAsElement.storeA in Hptr_split.
  rewrite <- sizeof_ptr in Hptr_split.
  sep_apply Hptr_split.
  sep_apply (row_blocks_missing_i_split_other_158 i j row_ptrs rows Hlen
    ltac:(lia) ltac:(lia) Hneq).
  Exists (Znth j row_ptrs 0).
  unfold char_ptr_array2_missing_two_158.
  Exists row_ptrs.
  entailer!.
  all: try rewrite sizeof_ptr; try lia; try entailer!.
  destruct (Z.ltb i j); entailer!.
Qed.

Lemma row_blocks_except_two_merge_missing_i_158 :
  forall i j row_ptrs rows,
  Zlength row_ptrs = Zlength rows ->
  0 <= i < Zlength rows ->
  0 <= j < Zlength rows ->
  i <> j ->
  CharArray.full (Znth j row_ptrs 0) (Zlength (Znth j rows nil)) (Znth j rows nil) **
  row_blocks_except_two_158 i j row_ptrs rows |--
  CharPtrArray2.row_blocks_missing_i i row_ptrs rows.
Proof.
  intros i j row_ptrs rows Hlen Hij Hjj Hneq.
  unfold CharPtrArray2.row_blocks_missing_i, row_blocks_except_two_158.
  destruct (Z.ltb_spec i j) as [Hij_lt | Hij_ge].
  - assert (Hidx : 0 <= j - 1 <
        Zlength (CharPtrArray2.remove_Znth i (combine row_ptrs rows))).
    {
      rewrite Zlength_remove_Znth_158.
      - rewrite CharPtrArray2.Zlength_combine_eq by auto. lia.
      - rewrite CharPtrArray2.Zlength_combine_eq by auto. lia.
    }
    assert (Hznth :
      Znth (j - 1)
        (CharPtrArray2.remove_Znth i (combine row_ptrs rows)) (0, nil) =
      (Znth j row_ptrs 0, Znth j rows nil)).
    {
      rewrite (Znth_remove_Znth_after_158
        (Z * list Z)%type i j (combine row_ptrs rows) (0, nil))
        by (try rewrite CharPtrArray2.Zlength_combine_eq by auto; lia).
      rewrite CharPtrArray2.Znth_combine by (auto; lia).
      reflexivity.
    }
    unfold CharPtrArray2.row_block at 1.
    change (CharPtrArray2.ElemArray.full
      (Znth j row_ptrs 0) (Zlength (Znth j rows nil)) (Znth j rows nil))
      with (CharArray.full
        (Znth j row_ptrs 0) (Zlength (Znth j rows nil))
        (Znth j rows nil)).
    sep_apply
      (CharPtrArray2.iter_sepcon_merge_remove_Znth
        CharPtrArray2.row_block (j - 1)
        (CharPtrArray2.remove_Znth i (combine row_ptrs rows))
        (Znth j row_ptrs 0, Znth j rows nil) Hidx).
    replace (Znth j row_ptrs 0, Znth j rows nil) with
      (Znth (j - 1)
        (CharPtrArray2.remove_Znth i (combine row_ptrs rows)) (0, nil))
      by (rewrite Hznth; reflexivity).
    rewrite replace_Znth_Znth by exact Hidx.
    entailer!.
  - assert (Hji : j < i) by lia.
    assert (Hidx : 0 <= j <
        Zlength (CharPtrArray2.remove_Znth i (combine row_ptrs rows))).
    {
      rewrite Zlength_remove_Znth_158.
      - rewrite CharPtrArray2.Zlength_combine_eq by auto. lia.
      - rewrite CharPtrArray2.Zlength_combine_eq by auto. lia.
    }
    assert (Hznth :
      Znth j
        (CharPtrArray2.remove_Znth i (combine row_ptrs rows)) (0, nil) =
      (Znth j row_ptrs 0, Znth j rows nil)).
    {
      rewrite (Znth_remove_Znth_before_158
        (Z * list Z)%type i j (combine row_ptrs rows) (0, nil))
        by (try rewrite CharPtrArray2.Zlength_combine_eq by auto; lia).
      rewrite CharPtrArray2.Znth_combine by (auto; lia).
      reflexivity.
    }
    unfold CharPtrArray2.row_block at 1.
    change (CharPtrArray2.ElemArray.full
      (Znth j row_ptrs 0) (Zlength (Znth j rows nil)) (Znth j rows nil))
      with (CharArray.full
        (Znth j row_ptrs 0) (Zlength (Znth j rows nil))
        (Znth j rows nil)).
    sep_apply
      (CharPtrArray2.iter_sepcon_merge_remove_Znth
        CharPtrArray2.row_block j
        (CharPtrArray2.remove_Znth i (combine row_ptrs rows))
        (Znth j row_ptrs 0, Znth j rows nil) Hidx).
    replace (Znth j row_ptrs 0, Znth j rows nil) with
      (Znth j
        (CharPtrArray2.remove_Znth i (combine row_ptrs rows)) (0, nil))
      by (rewrite Hznth; reflexivity).
    rewrite replace_Znth_Znth by exact Hidx.
    entailer!.
Qed.

Lemma char_ptr_array2_missing_two_merge_full_158 :
  forall x n i row_i j row_j rows,
  0 <= i < n ->
  0 <= j < n ->
  i <> j ->
  ((x + j * sizeof(PTR)) # Ptr |-> row_j) **
  CharArray.full row_j (Zlength (Znth j rows nil)) (Znth j rows nil) **
  CharArray.full row_i (Zlength (Znth i rows nil)) (Znth i rows nil) **
  char_ptr_array2_missing_two_158 x n i row_i j row_j rows |--
  CharPtrArray2.full x n rows.
Proof.
  intros x n i row_i j row_j rows Hi Hj Hneq.
  unfold char_ptr_array2_missing_two_158, CharPtrArray2.full.
  Intros row_ptrs.
  destruct H as [Hptrs [Hrows [Hi' [Hj' [Hneq' [Hrow_i Hrow_j]]]]]].
  subst row_i row_j.
  Exists row_ptrs.
  entailer!.
  assert (Hlen : Zlength row_ptrs = Zlength rows) by lia.
  assert (Hi_ptrs : 0 <= i < Zlength row_ptrs) by lia.
  eapply derivable1_trans with
    (y := (((x + j * sizeof(PTR)) # Ptr |-> Znth j row_ptrs 0) **
           PtrArray.missing_i x j 0 n row_ptrs) **
          (CharArray.full (Znth i row_ptrs 0)
             (Zlength (Znth i rows nil)) (Znth i rows nil) **
           (CharArray.full (Znth j row_ptrs 0)
              (Zlength (Znth j rows nil)) (Znth j rows nil) **
            row_blocks_except_two_158 i j row_ptrs rows))).
  { destruct (Z.ltb i j); entailer!. }
  pose proof (PtrArray.missing_i_merge_to_full
    x j n (Znth j row_ptrs 0) row_ptrs Hj) as Hptr_merge.
  unfold StorePtrAsElement.storeA in Hptr_merge.
  rewrite <- sizeof_ptr in Hptr_merge.
  sep_apply Hptr_merge.
  rewrite replace_Znth_Znth by lia.
  sep_apply (row_blocks_except_two_merge_missing_i_158
    i j row_ptrs rows Hlen ltac:(lia) ltac:(lia) Hneq).
  change (CharArray.full (Znth i row_ptrs 0)
    (Zlength (Znth i rows nil)) (Znth i rows nil))
    with (CharPtrArray2.ElemArray.full (Znth i row_ptrs 0)
      (Zlength (Znth i rows nil)) (Znth i rows nil)).
  sep_apply (CharPtrArray2.row_blocks_missing_i_merge_to_full
    i row_ptrs rows (Znth i rows nil) Hi_ptrs Hlen).
  rewrite replace_Znth_Znth by lia.
  entailer!.
Qed.

Lemma char_ptr_array2_missing_two_merge_full_cstring_158 :
  forall x n i row_i j row_j rows,
  rows_well_formed_158 rows n ->
  0 <= i < n ->
  0 <= j < n ->
  i <> j ->
  ((x + j * sizeof(PTR)) # Ptr |-> row_j) **
  CharArray.full row_j
    (string_lib.string_length (row_payload_z_158 (Znth j rows nil)) + 1)
    (string_lib.c_string (row_payload_z_158 (Znth j rows nil))) **
  CharArray.full row_i
    (string_lib.string_length (row_payload_z_158 (Znth i rows nil)) + 1)
    (string_lib.c_string (row_payload_z_158 (Znth i rows nil))) **
  char_ptr_array2_missing_two_158 x n i row_i j row_j rows |--
  CharPtrArray2.full x n rows.
Proof.
  intros x n i row_i j row_j rows Hwf Hi Hj Hneq.
  pose proof (rows_well_formed_158_row rows n i Hwf Hi) as Hrow_i.
  pose proof (rows_well_formed_158_row rows n j Hwf Hj) as Hrow_j.
  destruct Hrow_i as [Hrow_i [_ [_ [_ [_ Hlen_i]]]]].
  destruct Hrow_j as [Hrow_j [_ [_ [_ [_ Hlen_j]]]]].
  replace (string_lib.string_length (row_payload_z_158 (Znth i rows nil)) + 1)
    with (Zlength (Znth i rows nil)) by lia.
  replace (string_lib.string_length (row_payload_z_158 (Znth j rows nil)) + 1)
    with (Zlength (Znth j rows nil)) by lia.
  rewrite <- Hrow_i.
  rewrite <- Hrow_j.
  sep_apply (char_ptr_array2_missing_two_merge_full_158
    x n i row_i j row_j rows Hi Hj Hneq).
  entailer!.
Qed.

Lemma char_ptr_array2_missing_i_merge_full_158 :
  forall x n i row_i rows,
  0 <= i < n ->
  ((x + i * sizeof(PTR)) # Ptr |-> row_i) **
  CharArray.full row_i (Zlength (Znth i rows nil)) (Znth i rows nil) **
  CharPtrArray2.missing_i x n i row_i rows |--
  CharPtrArray2.full x n rows.
Proof.
  intros x n i row_i rows Hi.
  pose proof (CharPtrArray2.missing_i_merge_to_full
    x i n row_i rows (Znth i rows nil)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  rewrite <- sizeof_ptr in Hmerge.
  change (CharPtrArray2.ElemArray.full row_i
    (Zlength (Znth i rows nil)) (Znth i rows nil))
    with (CharArray.full row_i (Zlength (Znth i rows nil))
      (Znth i rows nil)) in Hmerge.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth; try lia.
  entailer!.
Qed.

Lemma string_le_refl_158 : forall s,
  string_le s s.
Proof.
  induction s as [|c s IH]; simpl; auto.
Qed.

Lemma string_le_trans_158 : forall s1 s2 s3,
  string_le s1 s2 ->
  string_le s2 s3 ->
  string_le s1 s3.
Proof.
  induction s1 as [|a s1 IH]; intros s2 s3 H12 H23.
  - simpl. exact I.
  - destruct s2 as [|b s2]; simpl in H12; [contradiction|].
    destruct s3 as [|c s3]; simpl in H23; [contradiction|].
    simpl in *.
    destruct H12 as [Hab | [Hab H12]];
    destruct H23 as [Hbc | [Hbc H23]].
    + left. lia.
    + subst c. left. exact Hab.
    + subst b. left. exact Hbc.
    + subst b c. right. split; [reflexivity|].
      eapply IH; eauto.
Qed.

Lemma row_unique_count_nonneg_158 : forall row,
  0 <= row_unique_count_z_158 row.
Proof.
  intros row.
  unfold row_unique_count_z_158.
  lia.
Qed.

Lemma valid_string_tail_158 : forall x xs,
  string_lib.valid_string (x :: xs) ->
  string_lib.valid_string xs.
Proof.
  intros x xs [Hascii Hno].
  split.
  - intros i Hi.
    specialize (Hascii (i + 1)).
    rewrite Zlength_cons in Hascii.
    rewrite Znth_cons in Hascii by lia.
    replace (i + 1 - 1) with i in Hascii by lia.
    apply Hascii. lia.
  - intros i Hi.
    specialize (Hno (i + 1)).
    rewrite Zlength_cons in Hno.
    rewrite Znth_cons in Hno by lia.
    replace (i + 1 - 1) with i in Hno by lia.
    apply Hno. lia.
Qed.

Lemma valid_string_head_bound_158 : forall x xs,
  string_lib.valid_string (x :: xs) ->
  0 <= x <= 127 /\ x <> 0.
Proof.
  intros x xs [Hascii Hno].
  split.
  - specialize (Hascii 0).
    rewrite Zlength_cons in Hascii.
    unfold Znth in Hascii. simpl in Hascii.
    apply Hascii.
    pose proof (Zlength_nonneg xs). lia.
  - specialize (Hno 0).
    rewrite Zlength_cons in Hno.
    unfold Znth in Hno. simpl in Hno.
    apply Hno.
    pose proof (Zlength_nonneg xs). lia.
Qed.

Lemma ascii_of_z_158_nat_of_ascii : forall z,
  0 <= z < 128 ->
  nat_of_ascii (ascii_of_z_158 z) = Z.to_nat z.
Proof.
  intros z Hz.
  unfold ascii_of_z_158.
  rewrite nat_ascii_embedding by lia.
  reflexivity.
Qed.

Lemma ascii_of_z_158_lt : forall x y,
  0 <= x < 128 ->
  0 <= y < 128 ->
  x < y ->
  (nat_of_ascii (ascii_of_z_158 x) <
   nat_of_ascii (ascii_of_z_158 y))%nat.
Proof.
  intros x y Hx Hy Hlt.
  rewrite !ascii_of_z_158_nat_of_ascii by lia.
  lia.
Qed.

Lemma c_string_cons_shift_158 : forall x xs k,
  0 <= k ->
  Znth (k + 1) (string_lib.c_string (x :: xs)) 0 =
  Znth k (string_lib.c_string xs) 0.
Proof.
  intros x xs k Hk.
  unfold string_lib.c_string.
  change ((x :: xs) ++ [0]) with (x :: (xs ++ [0])).
  rewrite Znth_cons by lia.
  replace (k + 1 - 1) with k by lia.
  reflexivity.
Qed.

Lemma strcmp_result_lt_string_le_158 : forall s1 s2 ret,
  string_lib.valid_string s1 ->
  string_lib.valid_string s2 ->
  string_lib.strcmp_result s1 s2 ret ->
  ret < 0 ->
  string_le (string_of_list_z_158 s1) (string_of_list_z_158 s2).
Proof.
  induction s1 as [|a s1_tail IH]; intros s2 ret Hvalid1 Hvalid2 Hcmp Hret.
  - simpl. exact I.
  - destruct Hcmp as [idx [Hidx1 [Hidx2 [Hpref [Hretdef Hstop]]]]].
    destruct s2 as [|b bs].
    + exfalso.
      unfold string_lib.string_length in Hidx2.
      rewrite Zlength_nil in Hidx2.
      assert (idx = 0) by lia. subst idx.
      rewrite string_lib.c_string_Znth_inside in Hretdef
        by (unfold string_lib.string_length; rewrite Zlength_cons;
            pose proof (Zlength_nonneg s1_tail); lia).
      change (Znth 0 (a :: s1_tail) 0) with a in Hretdef.
      change (Znth 0 (string_lib.c_string nil) 0) with 0 in Hretdef.
      destruct (valid_string_head_bound_158 a s1_tail Hvalid1) as [Ha _].
      lia.
    + simpl.
      destruct (Z.eq_dec idx 0) as [->|Hidx_ne].
      * rewrite string_lib.c_string_Znth_inside in Hretdef
          by (unfold string_lib.string_length; rewrite Zlength_cons;
              pose proof (Zlength_nonneg s1_tail); lia).
        rewrite string_lib.c_string_Znth_inside in Hretdef
          by (unfold string_lib.string_length; rewrite Zlength_cons;
              pose proof (Zlength_nonneg bs); lia).
        change (Znth 0 (a :: s1_tail) 0) with a in Hretdef.
        change (Znth 0 (b :: bs) 0) with b in Hretdef.
        left.
        destruct (valid_string_head_bound_158 a s1_tail Hvalid1) as [Ha _].
        destruct (valid_string_head_bound_158 b bs Hvalid2) as [Hb _].
        apply ascii_of_z_158_lt; lia.
      * right.
        assert (Hidx_pos : 0 < idx) by lia.
        assert (Hab : a = b).
        {
          specialize (Hpref 0 ltac:(lia)).
          rewrite string_lib.c_string_Znth_inside in Hpref.
          - rewrite string_lib.c_string_Znth_inside in Hpref.
            + exact Hpref.
            + unfold string_lib.string_length.
              rewrite Zlength_cons.
              pose proof (Zlength_nonneg bs). lia.
          - unfold string_lib.string_length.
            rewrite Zlength_cons.
            pose proof (Zlength_nonneg s1_tail). lia.
        }
        split; [subst; reflexivity|].
        apply IH with (ret := ret).
        -- apply valid_string_tail_158 in Hvalid1. exact Hvalid1.
        -- apply valid_string_tail_158 in Hvalid2. exact Hvalid2.
        -- exists (idx - 1).
           split.
           ++ unfold string_lib.string_length in *.
              rewrite Zlength_cons in Hidx1. lia.
           ++ split.
              ** unfold string_lib.string_length in *.
                 rewrite Zlength_cons in Hidx1.
                 rewrite Zlength_cons in Hidx2.
                 pose proof (Zlength_nonneg bs).
                 lia.
              ** split.
                 --- intros k Hk.
                     specialize (Hpref (k + 1) ltac:(lia)).
                     rewrite !c_string_cons_shift_158 in Hpref by lia.
                     exact Hpref.
                 --- split.
                     +++ rewrite Hretdef.
                         replace idx with (idx - 1 + 1) by lia.
                         rewrite !c_string_cons_shift_158 by lia.
                         replace (idx - 1 + 1 - 1) with (idx - 1) by lia.
                         reflexivity.
                    +++ replace idx with (idx - 1 + 1) in Hstop by lia.
                        rewrite !c_string_cons_shift_158 in Hstop by lia.
                        replace (idx - 1 + 1 - 1) with (idx - 1) in Hstop by lia.
                        exact Hstop.
        -- exact Hret.
Qed.

Lemma strcmp_result_ge_string_le_158 : forall s1 s2 ret,
  string_lib.valid_string s1 ->
  string_lib.valid_string s2 ->
  string_lib.strcmp_result s1 s2 ret ->
  ret >= 0 ->
  string_le (string_of_list_z_158 s2) (string_of_list_z_158 s1).
Proof.
  induction s1 as [|a s1_tail IH]; intros s2 ret Hvalid1 Hvalid2 Hcmp Hret.
  - destruct s2 as [|b bs].
    + simpl. exact I.
    + destruct Hcmp as [idx [Hidx1 [Hidx2 [Hpref [Hretdef Hstop]]]]].
      unfold string_lib.string_length in Hidx1.
      rewrite Zlength_nil in Hidx1.
      assert (idx = 0) by lia. subst idx.
      change (Znth 0 (string_lib.c_string nil) 0) with 0 in Hretdef.
      rewrite string_lib.c_string_Znth_inside in Hretdef
        by (unfold string_lib.string_length; rewrite Zlength_cons;
            pose proof (Zlength_nonneg bs); lia).
      change (Znth 0 (b :: bs) 0) with b in Hretdef.
      destruct (valid_string_head_bound_158 b bs Hvalid2) as [Hb Hb_nz].
      exfalso; lia.
  - destruct Hcmp as [idx [Hidx1 [Hidx2 [Hpref [Hretdef Hstop]]]]].
    destruct s2 as [|b bs].
    + simpl. exact I.
    + simpl.
      destruct (Z.eq_dec idx 0) as [->|Hidx_ne].
      * rewrite string_lib.c_string_Znth_inside in Hretdef
          by (unfold string_lib.string_length; rewrite Zlength_cons;
              pose proof (Zlength_nonneg s1_tail); lia).
        rewrite string_lib.c_string_Znth_inside in Hretdef
          by (unfold string_lib.string_length; rewrite Zlength_cons;
              pose proof (Zlength_nonneg bs); lia).
        change (Znth 0 (a :: s1_tail) 0) with a in Hretdef.
        change (Znth 0 (b :: bs) 0) with b in Hretdef.
        destruct (Z.eq_dec a b) as [Hab|Hab].
        -- subst b.
           destruct Hstop as [Hzero|Hneq].
           ++ destruct (valid_string_head_bound_158 a s1_tail Hvalid1) as [_ Hnz].
              contradiction.
           ++ contradiction.
        -- left.
           destruct (valid_string_head_bound_158 a s1_tail Hvalid1) as [Ha _].
           destruct (valid_string_head_bound_158 b bs Hvalid2) as [Hb _].
           apply ascii_of_z_158_lt; lia.
      * right.
        assert (Hidx_pos : 0 < idx) by lia.
        assert (Hab : a = b).
        {
          specialize (Hpref 0 ltac:(lia)).
          rewrite string_lib.c_string_Znth_inside in Hpref.
          - rewrite string_lib.c_string_Znth_inside in Hpref.
            + exact Hpref.
            + unfold string_lib.string_length.
              rewrite Zlength_cons.
              pose proof (Zlength_nonneg bs). lia.
          - unfold string_lib.string_length.
            rewrite Zlength_cons.
            pose proof (Zlength_nonneg s1_tail). lia.
        }
        split; [subst; reflexivity|].
        apply IH with (ret := ret).
        -- apply valid_string_tail_158 in Hvalid1. exact Hvalid1.
        -- apply valid_string_tail_158 in Hvalid2. exact Hvalid2.
        -- exists (idx - 1).
           split.
           ++ unfold string_lib.string_length in *.
              rewrite Zlength_cons in Hidx1. lia.
           ++ split.
              ** unfold string_lib.string_length in *.
                 rewrite Zlength_cons in Hidx1.
                 rewrite Zlength_cons in Hidx2.
                 pose proof (Zlength_nonneg bs).
                 lia.
              ** split.
                 --- intros k Hk.
                     specialize (Hpref (k + 1) ltac:(lia)).
                     rewrite !c_string_cons_shift_158 in Hpref by lia.
                     exact Hpref.
                 --- split.
                     +++ rewrite Hretdef.
                         replace idx with (idx - 1 + 1) by lia.
                         rewrite !c_string_cons_shift_158 by lia.
                         replace (idx - 1 + 1 - 1) with (idx - 1) by lia.
                         reflexivity.
                    +++ replace idx with (idx - 1 + 1) in Hstop by lia.
                        rewrite !c_string_cons_shift_158 in Hstop by lia.
                        replace (idx - 1 + 1 - 1) with (idx - 1) in Hstop by lia.
                        exact Hstop.
        -- exact Hret.
Qed.

Lemma best_prefix_state_158_step_keep : forall rows k best_idx maxu curu,
  best_prefix_state_158 rows k best_idx maxu ->
  0 <= k < Zlength rows ->
  curu = row_unique_count_z_158 (Znth k rows nil) ->
  curu <= maxu ->
  (curu = maxu ->
    string_le
      (row_string_z_158 (Znth best_idx rows nil))
      (row_string_z_158 (Znth k rows nil))) ->
  best_prefix_state_158 rows (k + 1) best_idx maxu.
Proof.
  intros rows k best_idx maxu curu Hst Hk Hcur Hle Htie.
  unfold best_prefix_state_158 in *.
  destruct Hst as [Hrange Hcase].
  split; [lia|].
  destruct Hcase as [[Hk0 [Hbest Hmax]] |
                     [Hkpos [Hbest_range [Hmax [Hall Hlex]]]]].
  - subst k best_idx maxu.
    right.
    assert (Hcur0 : row_unique_count_z_158 (Znth 0 rows nil) = 0).
    {
      subst curu.
      pose proof (row_unique_count_nonneg_158 (Znth 0 rows nil)).
      lia.
    }
    repeat split; try lia; auto.
    + intros j Hj.
      assert (j = 0) by lia. subst j. lia.
    + intros j Hj Hcnt.
      assert (j = 0) by lia. subst j.
      apply string_le_refl_158.
  - right.
    repeat split; try lia; auto.
    + intros j Hj.
      assert (j < k \/ j = k) as [Hlt | ->] by lia.
      * apply Hall; lia.
      * subst curu. exact Hle.
    + intros j Hj Hcnt.
      assert (j < k \/ j = k) as [Hlt | ->] by lia.
      * apply Hlex; auto; lia.
      * apply Htie.
        subst curu. exact Hcnt.
Qed.

Lemma best_prefix_state_158_step_update_strict : forall rows k best_idx maxu curu,
  best_prefix_state_158 rows k best_idx maxu ->
  0 <= k < Zlength rows ->
  curu = row_unique_count_z_158 (Znth k rows nil) ->
  maxu < curu ->
  best_prefix_state_158 rows (k + 1) k curu.
Proof.
  intros rows k best_idx maxu curu Hst Hk Hcur Hgt.
  unfold best_prefix_state_158 in *.
  destruct Hst as [Hrange Hcase].
  split; [lia|].
  right.
  repeat split; try lia; auto.
  - intros j Hj.
    assert (j < k \/ j = k) as [Hlt | ->] by lia.
    + destruct Hcase as [[Hk0 _] |
                         [_ [_ [_ [Hall _]]]]].
      * lia.
      * specialize (Hall j ltac:(lia)). lia.
    + subst curu. lia.
  - intros j Hj Hcnt.
    assert (j < k \/ j = k) as [Hlt | ->] by lia.
    + destruct Hcase as [[Hk0 _] |
                         [_ [_ [_ [Hall _]]]]].
      * lia.
      * specialize (Hall j ltac:(lia)). lia.
    + apply string_le_refl_158.
Qed.

Lemma best_prefix_state_158_step_update_tie : forall rows k best_idx maxu curu,
  best_prefix_state_158 rows k best_idx maxu ->
  0 <= k < Zlength rows ->
  curu = row_unique_count_z_158 (Znth k rows nil) ->
  curu = maxu ->
  string_le
    (row_string_z_158 (Znth k rows nil))
    (row_string_z_158 (Znth best_idx rows nil)) ->
  best_prefix_state_158 rows (k + 1) k curu.
Proof.
  intros rows k best_idx maxu curu Hst Hk Hcur Htie_count Htie_lex.
  unfold best_prefix_state_158 in *.
  destruct Hst as [Hrange Hcase].
  split; [lia|].
  right.
  split; [lia|].
  split; [lia|].
  split; [exact Hcur|].
  split.
  - intros j Hj.
    assert (j < k \/ j = k) as [Hlt | ->] by lia.
    + destruct Hcase as [[Hk0 _] |
                         [_ [_ [Hmax [Hall _]]]]].
      * lia.
      * specialize (Hall j ltac:(lia)). subst curu. lia.
    + subst curu. lia.
  - intros j Hj Hcnt.
    assert (j < k \/ j = k) as [Hlt | ->] by lia.
    + destruct Hcase as [[Hk0 _] |
                         [_ [_ [Hmax [_ Hlex]]]]].
      * lia.
      * eapply string_le_trans_158.
        -- exact Htie_lex.
        -- apply Hlex.
           ++ lia.
           ++ subst curu. lia.
    + apply string_le_refl_158.
Qed.

Lemma Znth_In_range_158 : forall {A : Type} (l : list A) i d,
  0 <= i < Zlength l ->
  In (Znth i l d) l.
Proof.
  intros A l i d Hi.
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hi.
  lia.
Qed.

Lemma In_Znth_exists_158 : forall {A : Type} (x : A) l d,
  In x l ->
  exists i, 0 <= i < Zlength l /\ Znth i l d = x.
Proof.
  intros A x l d Hin.
  apply In_nth_error in Hin.
  destruct Hin as [n Hn].
  exists (Z.of_nat n).
  split.
  - assert ((n < List.length l)%nat) as Hlt.
    { apply nth_error_Some. rewrite Hn. discriminate. }
    rewrite Zlength_correct. lia.
  - unfold Znth.
    rewrite Nat2Z.id.
    apply nth_error_nth with (d := d) in Hn.
    exact Hn.
Qed.

Lemma best_prefix_state_158_final_spec : forall rows n best_idx maxu,
  rows_well_formed_158 rows n ->
  problem_158_pre_z rows ->
  0 < n ->
  best_prefix_state_158 rows n best_idx maxu ->
  problem_158_spec_z rows best_idx.
Proof.
  intros rows n best_idx maxu Hwf _ Hnpos Hst.
  unfold problem_158_spec_z, problem_158_spec, rows_to_strings_z_158.
  unfold best_prefix_state_158 in Hst.
  destruct Hwf as [Hrows_len Hwf].
  destruct Hst as [Hrange Hcase].
  destruct Hcase as [[Hn0 _] |
                     [Hnpos_state [Hbest_range [Hmax [Hall Hlex]]]]].
  - lia.
  - split.
    + apply in_map.
      apply Znth_In_range_158.
      lia.
    + intros w Hin.
      apply in_map_iff in Hin.
      destruct Hin as [row [Hw Hinrow]].
      destruct (In_Znth_exists_158 row rows nil Hinrow)
        as [j [Hj Hrow]].
      subst w.
      rewrite <- Hrow.
      specialize (Hall j ltac:(lia)).
      destruct (Z_lt_ge_dec
        (row_unique_count_z_158 (Znth j rows nil)) maxu) as [Hlt | Hge].
      * left.
        unfold row_unique_count_z_158 in Hlt, Hmax.
        apply Nat2Z.inj_gt.
        lia.
      * right.
        split.
        -- unfold row_unique_count_z_158 in Hge, Hall, Hmax.
           apply Nat2Z.inj.
           lia.
        -- apply Hlex.
           ++ lia.
           ++ lia.
Qed.

Lemma zeros_snoc_158 : forall k,
  0 <= k ->
  zeros k ++ [0] = zeros (k + 1).
Proof.
  intros k Hk.
  symmetry.
  unfold zeros.
  replace (Z.to_nat (k + 1)) with (Z.to_nat k + 1)%nat by lia.
  rewrite repeat_app.
  reflexivity.
Qed.

Lemma reset_prefix_state_158_initial : forall seen_l,
  Zlength seen_l = 128 ->
  reset_prefix_state_158 0 seen_l.
Proof.
  intros seen_l Hlen.
  unfold reset_prefix_state_158.
  repeat split; try lia.
Qed.

Lemma reset_prefix_state_158_step : forall k seen_l,
  reset_prefix_state_158 k seen_l ->
  0 <= k < 128 ->
  reset_prefix_state_158 (k + 1) (replace_Znth k 0 seen_l).
Proof.
  intros k seen_l [Hrange [Hlen Hzero]] Hk.
  unfold reset_prefix_state_158.
  split; [lia|].
  split; [rewrite Zlength_replace_Znth; lia|].
  intros c Hc.
  destruct (Z.eq_dec c k) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same; lia.
  - rewrite Znth_replace_Znth_Diff by lia.
    apply Hzero; lia.
Qed.

Lemma reset_prefix_state_158_full_zero : forall k seen_l,
  reset_prefix_state_158 k seen_l ->
  k >= 128 ->
  k <= 128 ->
  seen_l = zeros 128.
Proof.
  intros k seen_l [Hrange [Hlen Hzero]] Hge Hle.
  apply (proj2 (list_eq_ext seen_l (zeros 128) 0)).
  split.
  - rewrite Hlen. unfold zeros. rewrite Zlength_correct, repeat_length. lia.
  - intros i Hi.
    rewrite Hlen in Hi.
    rewrite Hzero by lia.
    unfold zeros.
    rewrite Znth_repeat by lia.
    reflexivity.
Qed.

Lemma count_scan_state_158_initial : forall row,
  count_scan_state_158 row 0 (zeros 128) 0.
Proof.
  intros row.
  unfold count_scan_state_158.
  refine (conj _ (conj _ (conj _ _))).
  - unfold string_lib.string_length. pose proof (Zlength_nonneg (row_payload_z_158 row)). lia.
  - unfold zeros. rewrite Zlength_correct, repeat_length. lia.
  - intros c Hc.
    left.
    split.
    + unfold zeros. rewrite Znth_repeat by lia. reflexivity.
    + intros [_ [p [Hp _]]]. lia.
  - simpl. reflexivity.
Qed.

Lemma count_scan_state_158_step_new : forall row j seen_l unique ch,
  string_lib.valid_string (row_payload_z_158 row) ->
  count_scan_state_158 row j seen_l unique ->
  0 <= j < string_lib.string_length (row_payload_z_158 row) ->
  0 <= ch < 128 ->
  ch = Znth j (row_payload_z_158 row) 0 ->
  Znth ch seen_l 0 = 0 ->
  count_scan_state_158 row (j + 1) (replace_Znth ch 1 seen_l) (unique + 1).
Proof.
  intros row j seen_l unique ch Hvalid Hst Hj Hch_range Hch Hzero.
  unfold count_scan_state_158 in *.
  destruct Hst as [Hrange [Hlen [Hmap Huniq]]].
  destruct Hvalid as [Hascii _].
  refine (conj _ (conj _ (conj _ _))).
  - lia.
  - rewrite Zlength_replace_Znth; lia.
  - intros c Hc.
    destruct (Z.eq_dec c ch) as [->|Hneq].
    + right.
      split.
      * rewrite Znth_replace_Znth_Same; lia.
      * unfold byte_seen_158.
        split; [lia|].
        exists j. split; [lia|symmetry; exact Hch].
    + rewrite Znth_replace_Znth_Diff by lia.
      specialize (Hmap c Hc).
      destruct Hmap as [[Hseen Hnot_seen]|[Hseen Hseen_prop]].
      * left.
        split; [exact Hseen|].
        intros Hnew.
        unfold byte_seen_158 in Hnew.
        destruct Hnew as [_ [p [Hp Hpayload]]].
        assert (p < j \/ p = j) as [Hplt|Hp_eq] by lia.
        -- apply Hnot_seen.
           unfold byte_seen_158.
           split; [lia|].
           exists p. split; [lia|exact Hpayload].
        -- subst p. congruence.
      * right.
        split; [exact Hseen|].
        unfold byte_seen_158 in *.
        destruct Hseen_prop as [Hcr [p [Hp Hpayload]]].
        split; [exact Hcr|].
        exists p. split; [lia|exact Hpayload].
  - rewrite Huniq.
    rewrite (firstn_succ_Znth_158 (row_payload_z_158 row) j 0)
      by (unfold string_lib.string_length in Hj; lia).
    rewrite string_of_list_z_158_app.
    simpl.
    rewrite <- Hch.
    rewrite count_unique_chars_snoc_new_158.
    + lia.
    + apply string_contains_string_of_list_z_158_false.
      * apply all_ascii_firstn_158. exact Hascii.
      * exact Hch_range.
      * intros p Hp Hpayload.
        specialize (Hmap ch Hch_range).
        rewrite Hzero in Hmap.
        destruct Hmap as [[_ Hnot_seen]|[Hone _]]; [|lia].
        apply Hnot_seen.
        unfold byte_seen_158.
        split; [exact Hch_range|].
        exists p.
        split.
        -- rewrite Zlength_correct in Hp.
           rewrite length_firstn in Hp.
           lia.
        -- unfold Znth in Hpayload |- *.
           rewrite nth_firstn in Hpayload.
           exact Hpayload.
           rewrite Zlength_correct in Hp.
           rewrite length_firstn in Hp.
           lia.
Qed.

Lemma count_scan_state_158_step_seen : forall row j seen_l unique ch,
  count_scan_state_158 row j seen_l unique ->
  0 <= j < string_lib.string_length (row_payload_z_158 row) ->
  0 <= ch < 128 ->
  ch = Znth j (row_payload_z_158 row) 0 ->
  Znth ch seen_l 0 <> 0 ->
  count_scan_state_158 row (j + 1) seen_l unique.
Proof.
  intros row j seen_l unique ch Hst Hj Hch_range Hch Hnonzero.
  unfold count_scan_state_158 in *.
  destruct Hst as [Hrange [Hlen [Hmap Huniq]]].
  refine (conj _ (conj _ (conj _ _))).
  - lia.
  - exact Hlen.
  - intros c Hc.
    specialize (Hmap c Hc).
    destruct Hmap as [[Hseen Hnot_seen]|[Hseen Hseen_prop]].
    + left.
      split; [exact Hseen|].
      intros Hnew.
      unfold byte_seen_158 in Hnew.
      destruct Hnew as [_ [p [Hp Hpayload]]].
      assert (p < j \/ p = j) as [Hplt|Hp_eq] by lia.
      * apply Hnot_seen.
        unfold byte_seen_158.
        split; [exact Hc|].
        exists p. split; [lia|exact Hpayload].
      * subst p.
        assert (c = ch) by congruence.
        subst c. rewrite <- Hch in Hseen.
        rewrite Hseen in Hnonzero. contradiction.
    + right.
      split; [exact Hseen|].
      unfold byte_seen_158 in *.
      destruct Hseen_prop as [Hcr [p [Hp Hpayload]]].
      split; [exact Hcr|].
      exists p. split; [lia|exact Hpayload].
  - rewrite Huniq.
    rewrite (firstn_succ_Znth_158 (row_payload_z_158 row) j 0)
      by (unfold string_lib.string_length in Hj; lia).
    rewrite string_of_list_z_158_app.
    simpl.
    rewrite <- Hch.
    rewrite count_unique_chars_snoc_seen_158.
    + reflexivity.
    + specialize (Hmap ch Hch_range).
      destruct Hmap as [[Hzero _]|[Hone Hseen_prop]].
      * contradiction.
      * unfold byte_seen_158 in Hseen_prop.
        destruct Hseen_prop as [_ [p [Hp Hpayload]]].
        apply string_contains_string_of_list_z_158_true_at with (p := p).
        -- rewrite Zlength_correct.
           rewrite length_firstn.
           replace (Z.of_nat (Init.Nat.min (Z.to_nat j)
             (List.length (row_payload_z_158 row)))) with j
             by (unfold string_lib.string_length in Hj;
                 rewrite Zlength_correct in Hj; lia).
           lia.
        -- unfold Znth in Hpayload |- *.
           rewrite nth_firstn.
           symmetry. exact Hpayload.
           lia.
Qed.

Lemma count_scan_state_158_complete : forall row seen_l unique,
  count_scan_state_158
    row (string_lib.string_length (row_payload_z_158 row)) seen_l unique ->
  unique = row_unique_count_z_158 row.
Proof.
  intros row seen_l unique Hst.
  unfold count_scan_state_158 in Hst.
  destruct Hst as [_ [_ [_ Huniq]]].
  unfold row_unique_count_z_158, row_string_z_158.
  rewrite Huniq.
  f_equal.
  f_equal.
  unfold string_lib.string_length.
  rewrite Zlength_correct, Nat2Z.id.
  rewrite firstn_all.
  reflexivity.
Qed.

Lemma best_prefix_state_158_initial : forall rows,
  best_prefix_state_158 rows 0 0 0.
Proof.
  intros rows.
  unfold best_prefix_state_158.
  split.
  - rewrite Zlength_correct. lia.
  - left; repeat split; reflexivity.
Qed.
End MigratedCompanionProofs.
Export MigratedCompanionProofs.
(* END migrated companion-spec proofs *)

Lemma proof_of_find_max_entail_wit_1 : find_max_entail_wit_1.
Proof.
  pre_process_default.
  unfold zeros; simpl.
  rewrite IntArray.seg_empty.
  entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_2 : find_max_entail_wit_2.
Proof.
  pre_process_default.
  rewrite zeros_snoc_158 by lia.
  entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_3 : find_max_entail_wit_3.
Proof.
  pre_process_default.
  subst.
  Exists (zeros 128).
  replace k with 128 by lia.
  rewrite (IntArray.undef_seg_empty ( &( "seen" ) ) 128).
  sep_apply (IntArray.seg_to_full ( &( "seen" ) ) 0 128 (zeros 128)).
  replace ((&( "seen" ) + 0 * sizeof(INT))) with (&( "seen" )) by lia.
  replace (128 - 0) with 128 by lia.
  entailer!.
  apply best_prefix_state_158_initial.
Qed.

Lemma proof_of_find_max_entail_wit_4 : find_max_entail_wit_4.
Proof.
  pre_process_default.
  prop_apply (CharPtrArray2.full_Zlength words_pre words_size_pre rows).
  Intros.
  sep_apply_l_atomic (CharPtrArray2.full_split_to_missing_i words_pre i words_size_pre rows).
  - dump_pre_spatial. lia.
  - Intros row_ptr.
    Exists row_ptr seen_l_2.
    unfold StorePtrAsElement.storeA.
    rewrite sizeof_ptr.
    repeat match goal with
    | |- context [Znth i rows ?d] => rewrite (Znth_indep rows i nil d) by lia
    end.
    entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_5 : find_max_entail_wit_5.
Proof.
  pre_process_default.
  Exists row_ptr_2 seen_l_2.
  entailer!.
  apply reset_prefix_state_158_initial; auto.
Qed.

Lemma proof_of_find_max_entail_wit_6 : find_max_entail_wit_6.
Proof.
  pre_process_default.
  Exists row_ptr_2 (replace_Znth k 0 seen_l_2).
  entailer!.
  - apply reset_prefix_state_158_step; auto; lia.
  - rewrite Zlength_replace_Znth; lia.
Qed.

Lemma proof_of_find_max_entail_wit_7 : find_max_entail_wit_7.
Proof.
  pre_process_default.
  assert (seen_l = zeros 128) as ->.
  { eapply reset_prefix_state_158_full_zero; eauto; lia. }
  Exists row_ptr_2.
  entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_8 : find_max_entail_wit_8.
Proof.
  pre_process_default.
  match goal with
  | Hwf : rows_well_formed_158 rows words_size_pre |- _ =>
      pose proof (rows_well_formed_158_row rows words_size_pre i Hwf ltac:(lia)) as Hrow_info
  end.
  destruct Hrow_info as [Hrow [Hvalid [Hlt [_ [_ Hlen]]]]].
  rewrite Hrow.
  unfold store_string.
  rewrite row_payload_c_string_158.
  rewrite c_string_Zlength_158.
  entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_9 : find_max_entail_wit_9.
Proof.
  pre_process_default.
  Exists (zeros 128).
  match goal with
  | Hwf : rows_well_formed_158 rows words_size_pre |- _ =>
      pose proof (rows_well_formed_158_row rows words_size_pre i Hwf ltac:(lia))
        as Hrow_info
  end.
  destruct Hrow_info as [Hrow [Hvalid [Hlt [Hprefix [Hbound Hlen]]]]].
  assert (0 <= retval) by (rewrite PreH1; unfold string_length; apply Zlength_nonneg).
  unfold store_string.
  rewrite <- Hrow.
  rewrite <- Hlen.
  entailer!.
  apply count_scan_state_158_initial.
Qed.

Lemma proof_of_find_max_entail_wit_10 : find_max_entail_wit_10.
Proof.
  pre_process_default.
  match goal with
  | Hwf : rows_well_formed_158 rows words_size_pre |- _ =>
      pose proof (rows_well_formed_158_char_bound rows words_size_pre i j
        Hwf ltac:(lia) ltac:(lia)) as Hchar_bound
  end.
  Exists seen_l_2.
  entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_11_1 : find_max_entail_wit_11_1.
Proof.
  pre_process_default.
  pose proof (rows_well_formed_158_row rows words_size_pre i PreH22 ltac:(lia))
    as Hrow_info.
  destruct Hrow_info as [Hrow [Hvalid [Hlt [Hprefix [Hbound Hlen]]]]].
  assert (Hch_payload : ch = Znth j (row_payload_z_158 (Znth i rows nil)) 0).
  {
    rewrite Hrow in PreH11.
    rewrite string_lib.c_string_Znth_inside in PreH11 by (rewrite <- PreH18; lia).
    exact PreH11.
  }
  assert (Hnew_state :
    count_scan_state_158
      (Znth i rows nil) (j + 1) (replace_Znth ch 1 seen_l_2) (unique + 1)).
  { eapply count_scan_state_158_step_new; eauto; lia. }
  assert (Hunique_bound : unique + 1 <= 128).
  {
    unfold count_scan_state_158 in Hnew_state.
    destruct Hnew_state as [_ [_ [_ Huniq_new]]].
    rewrite Huniq_new.
    apply Hprefix. rewrite <- PreH18. lia.
  }
  Exists (replace_Znth ch 1 seen_l_2).
  entailer!.
  rewrite Zlength_replace_Znth; lia.
Qed.

Lemma proof_of_find_max_entail_wit_11_2 : find_max_entail_wit_11_2.
Proof.
  pre_process_default.
  pose proof (rows_well_formed_158_row rows words_size_pre i PreH22 ltac:(lia))
    as Hrow_info.
  destruct Hrow_info as [Hrow [Hvalid [Hlt [Hprefix [Hbound Hlen]]]]].
  assert (Hch_payload : ch = Znth j (row_payload_z_158 (Znth i rows nil)) 0).
  {
    rewrite Hrow in PreH11.
    rewrite string_lib.c_string_Znth_inside in PreH11 by (rewrite <- PreH18; lia).
    exact PreH11.
  }
  Exists seen_l_2.
  entailer!.
  eapply count_scan_state_158_step_seen; eauto; lia.
Qed.

Lemma proof_of_find_max_entail_wit_12 : find_max_entail_wit_12.
Proof.
  pre_process_default.
  assert (Hj_len : j = string_lib.string_length (row_payload_z_158 (Znth i rows nil))).
  { rewrite <- PreH17. lia. }
  assert (Hunique_final : unique = row_unique_count_z_158 (Znth i rows nil)).
  {
    rewrite Hj_len in PreH26.
    eapply count_scan_state_158_complete; exact PreH26.
  }
  pose proof (rows_well_formed_158_row rows words_size_pre i PreH23 ltac:(lia))
    as Hcur_info.
  pose proof (rows_well_formed_158_row rows words_size_pre best_idx PreH23 ltac:(lia))
    as Hbest_info.
  destruct Hcur_info as [Hcur_row [Hcur_valid [Hcur_lt [_ [_ Hcur_len]]]]].
  destruct Hbest_info as [Hbest_row [Hbest_valid [Hbest_lt [_ [_ Hbest_len]]]]].
  sep_apply_l_atomic
    (char_ptr_array2_missing_i_split_two_158
      words_pre words_size_pre i best_idx row_ptr rows ltac:(lia) ltac:(lia) PreH1).
  Intros best_ptr.
  Exists best_ptr seen_l_2.
  rewrite Hcur_row in Hcur_len.
  rewrite Hbest_row in Hbest_len.
  rewrite Hcur_row.
  rewrite Hbest_row.
  rewrite !row_payload_c_string_158 in *.
  unfold store_string.
  rewrite <- Hcur_len, <- Hbest_len.
  entailer!.
  rewrite <- Hcur_row.
  exact Hunique_final.
Qed.

Lemma proof_of_find_max_entail_wit_15_1 : find_max_entail_wit_15_1.
Proof.
  pre_process_default.
  - assert (Hj_len : j = string_lib.string_length (row_payload_z_158 (Znth i rows nil))).
    { rewrite <- PreH17. lia. }
    assert (Hunique_final : unique = row_unique_count_z_158 (Znth i rows nil)).
    {
      rewrite Hj_len in PreH26.
      eapply count_scan_state_158_complete; exact PreH26.
    }
    pose proof (proj1 PreH23) as Hrows_len.
    pose proof (rows_well_formed_158_row rows words_size_pre i PreH23 ltac:(lia))
      as Hrow_info.
    destruct Hrow_info as [_ [_ [Hlen_lt [_ [_ _]]]]].
    assert (Hstep : best_prefix_state_158 rows (i + 1) best_idx maxu).
    {
      eapply best_prefix_state_158_step_keep
        with (curu := unique); eauto; try lia.
      intros _.
      subst best_idx.
      apply string_le_refl_158.
    }
    sep_apply_l_atomic
      (char_ptr_array2_missing_i_merge_full_158
        words_pre words_size_pre i row_ptr rows ltac:(lia)).
    Exists seen_l_2.
    entailer!.
  Unshelve.
  all: try lia; try entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_15_2 : find_max_entail_wit_15_2.
Proof.
  pre_process_default.
  assert (Hj_len : j = string_lib.string_length (row_payload_z_158 (Znth i rows nil))).
  { rewrite <- PreH16. lia. }
  assert (Hunique_final : unique = row_unique_count_z_158 (Znth i rows nil)).
  {
    rewrite Hj_len in PreH25.
    eapply count_scan_state_158_complete; exact PreH25.
  }
  pose proof (proj1 PreH22) as Hrows_len.
  pose proof (rows_well_formed_158_row rows words_size_pre i PreH22 ltac:(lia))
    as Hrow_info.
  destruct Hrow_info as [_ [_ [Hlen_lt [_ [_ _]]]]].
  assert (Hstep : best_prefix_state_158 rows (i + 1) best_idx maxu).
  {
    eapply best_prefix_state_158_step_keep
      with (curu := unique); eauto; try lia.
  }
  sep_apply_l_atomic
    (char_ptr_array2_missing_i_merge_full_158
      words_pre words_size_pre i row_ptr rows ltac:(lia)).
  Exists seen_l_2.
  entailer!.
  Unshelve.
  all: try lia; try entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_15_3 : find_max_entail_wit_15_3.
Proof.
  right.
  pre_process_default.
  pose proof (proj1 PreH17) as Hrows_len.
  assert (Hstep : best_prefix_state_158 rows (i + 1) best_idx maxu).
  {
    eapply best_prefix_state_158_step_keep
      with (curu := unique).
    - exact PreH19.
    - lia.
    - exact PreH11.
    - lia.
    - intros _.
      subst unique.
      eapply strcmp_result_ge_string_le_158; eauto; lia.
  }
  sep_apply_l_atomic
    (char_ptr_array2_missing_two_merge_full_cstring_158
      words_pre words_size_pre i row_ptr best_idx best_ptr rows
      PreH17 ltac:(lia) ltac:(lia) ltac:(lia)).
  entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_15_4 : find_max_entail_wit_15_4.
Proof.
  right.
  pre_process_default.
  pose proof (proj1 PreH17) as Hrows_len.
  assert (Htie :
    string_le
      (row_string_z_158 (Znth i rows nil))
      (row_string_z_158 (Znth best_idx rows nil))).
  {
    eapply strcmp_result_lt_string_le_158; eauto; lia.
  }
  assert (Hstep : best_prefix_state_158 rows (i + 1) i maxu).
  {
    assert (Hstep_unique : best_prefix_state_158 rows (i + 1) i unique).
    {
      eapply best_prefix_state_158_step_update_tie
        with (best_idx := best_idx) (maxu := maxu); eauto; try lia.
    }
    rewrite PreH12 in Hstep_unique.
    exact Hstep_unique.
  }
  sep_apply_l_atomic
    (char_ptr_array2_missing_two_merge_full_cstring_158
      words_pre words_size_pre i row_ptr best_idx best_ptr rows
      PreH17 ltac:(lia) ltac:(lia) ltac:(lia)).
  entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_15_5 : find_max_entail_wit_15_5.
Proof.
  pre_process_default.
  assert (Hj_len : j = string_lib.string_length (row_payload_z_158 (Znth i rows nil))).
  { rewrite <- PreH15. lia. }
  assert (Hunique_final : unique = row_unique_count_z_158 (Znth i rows nil)).
  {
    rewrite Hj_len in PreH24.
    eapply count_scan_state_158_complete; exact PreH24.
  }
  pose proof (rows_well_formed_158_row rows words_size_pre i PreH21 ltac:(lia))
    as Hrow_info.
  pose proof (proj1 PreH21) as Hrows_len.
  destruct Hrow_info as [_ [_ [Hlen_lt [_ [_ _]]]]].
  assert (Hstep : best_prefix_state_158 rows (i + 1) i unique).
  {
    eapply best_prefix_state_158_step_update_strict
      with (best_idx := best_idx) (maxu := maxu).
    - exact PreH23.
    - lia.
    - exact Hunique_final.
    - lia.
  }
  sep_apply_l_atomic
    (char_ptr_array2_missing_i_merge_full_158
      words_pre words_size_pre i row_ptr rows ltac:(lia)).
  Exists seen_l_2.
  entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_17 : find_max_entail_wit_17.
Proof.
  pre_process_default.
  assert (Hi_end : i = words_size_pre) by lia.
  subst i.
  assert (Hspec : problem_158_spec_z rows best_idx).
  {
    eapply best_prefix_state_158_final_spec; eauto; lia.
  }
  prop_apply (CharPtrArray2.full_Zlength words_pre words_size_pre rows).
  Intros.
  sep_apply_l_atomic
    (CharPtrArray2.full_split_to_missing_i
      words_pre best_idx words_size_pre rows).
  - dump_pre_spatial. lia.
  - Intros row_ptr.
    Exists row_ptr seen_l_2.
    unfold StorePtrAsElement.storeA.
    rewrite sizeof_ptr.
    repeat match goal with
    | |- context [Znth best_idx rows ?d] =>
        rewrite (Znth_indep rows best_idx nil d) by lia
    end.
    entailer!.
Qed.
