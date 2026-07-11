(* Given a list of strings, where each string consists of only digits, return a list.
Each element i of the output should be "the number of odd elements in the
string i of the input." where all the i's should be replaced by the number
of odd digits in the i'th string of the input.

>>> odd_count(['1234567'])
["the number of odd elements 4n the str4ng 4 of the 4nput."]
>>> odd_count(['3',"11111111"])
["the number of odd elements 1n the str1ng 1 of the 1nput.",
"the number of odd elements 8n the str8ng 8 of the 8nput."] *)

Require Import Coq.Strings.String Coq.Lists.List Coq.Strings.Ascii.
Require Import Coq.NArith.NArith Coq.Numbers.DecimalString.
Import ListNotations.


Definition is_odd_digit (c : ascii) : bool :=
  match c with "1"%char|"3"%char|"5"%char|"7"%char|"9"%char => true | _ => false end.

Definition count_odd_digits (s : string) : nat :=
  List.length (List.filter is_odd_digit (list_ascii_of_string s)).

Definition nat_to_string (n : nat) : string :=
  NilZero.string_of_uint (N.to_uint (N.of_nat n)).

Definition replace_char_with_string (target : ascii) (replacement : string) (s : string) : string :=
  string_of_list_ascii
    (List.flat_map
       (fun c =>
          if Ascii.eqb c target
          then list_ascii_of_string replacement
          else [c])
       (list_ascii_of_string s)).

Definition process_string (s : string) : string :=
  let cnt := count_odd_digits s in
  let cnt_str := nat_to_string cnt in
  let templ := "the number of odd elements in the string i of the input."%string in
  replace_char_with_string "i"%char cnt_str templ.

Definition odd_count_impl (input : list string) : list string := map process_string input.

(* 每个字符串只包含数字字符 *)
Definition problem_113_pre (input : list string) : Prop :=
  Forall (fun s =>
    Forall (fun ch =>
      let n := nat_of_ascii ch in 48 <= n /\ n <= 57)
      (list_ascii_of_string s)) input.

Definition problem_113_spec (input : list string) (output : list string) : Prop :=
  output = odd_count_impl input.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import SimpleC.StdLib.string_lib.

Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Import naive_C_Rules.
Local Open Scope sac.

Parameter LitMap : string -> addr.

Definition nil_z_113 : list Z := nil.

Definition row_at_113 (i : Z) (rows : list (list Z)) : list Z :=
  Znth i rows nil_z_113.

Definition ascii_of_z_113 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_113 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_113 c) (string_of_list_z_113 rest)
  end.

Definition row_payload_z_113 (row : list Z) : list Z :=
  firstn (Z.to_nat (Zlength row - 1)) row.

Definition row_string_z_113 (row : list Z) : string :=
  string_of_list_z_113 (row_payload_z_113 row).

Definition rows_to_strings_z_113 (rows : list (list Z)) : list string :=
  map row_string_z_113 rows.

Definition problem_113_pre_z (rows : list (list Z)) : Prop :=
  problem_113_pre (rows_to_strings_z_113 rows).

Definition problem_113_spec_z
    (rows output_rows : list (list Z)) : Prop :=
  problem_113_spec
    (rows_to_strings_z_113 rows)
    (rows_to_strings_z_113 output_rows).

Definition rows_well_formed_113 (rows : list (list Z)) (n : Z) : Prop :=
  Zlength rows = n /\
  forall k,
    0 <= k < n ->
    let row := Znth k rows nil in
    let payload := row_payload_z_113 row in
    row = c_string payload /\
    valid_string payload /\
    all_ascii payload /\
    string_length payload < INT_MAX.

Definition is_odd_digit_z_113 (c : Z) : bool :=
  Z.eqb c 49 || Z.eqb c 51 || Z.eqb c 53 || Z.eqb c 55 || Z.eqb c 57.

Fixpoint count_odd_digits_payload_113 (s : list Z) : Z :=
  match s with
  | [] => 0
  | c :: rest =>
      (if is_odd_digit_z_113 c then 1 else 0) +
      count_odd_digits_payload_113 rest
  end.

Definition odd_digit_count_prefix_113 (s : list Z) (i : Z) : Z :=
  count_odd_digits_payload_113 (sublist 0 i s).

Definition odd_digit_count_row_113 (row : list Z) : Z :=
  count_odd_digits_payload_113 (row_payload_z_113 row).

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

Fixpoint uint_digits_z_113 (d : Decimal.uint) : list Z :=
  match d with
  | Decimal.Nil => []
  | Decimal.D0 rest => 48 :: uint_digits_z_113 rest
  | Decimal.D1 rest => 49 :: uint_digits_z_113 rest
  | Decimal.D2 rest => 50 :: uint_digits_z_113 rest
  | Decimal.D3 rest => 51 :: uint_digits_z_113 rest
  | Decimal.D4 rest => 52 :: uint_digits_z_113 rest
  | Decimal.D5 rest => 53 :: uint_digits_z_113 rest
  | Decimal.D6 rest => 54 :: uint_digits_z_113 rest
  | Decimal.D7 rest => 55 :: uint_digits_z_113 rest
  | Decimal.D8 rest => 56 :: uint_digits_z_113 rest
  | Decimal.D9 rest => 57 :: uint_digits_z_113 rest
  end.

Definition decimal_digits_113 (n : Z) : list Z :=
  match N.to_uint (N.of_nat (Z.to_nat n)) with
  | Decimal.Nil => [48]
  | d => uint_digits_z_113 d
  end.

Definition template_payload_113 : list Z :=
  [116; 104; 101; 32; 110; 117; 109; 98; 101; 114; 32; 111; 102; 32;
   111; 100; 100; 32; 101; 108; 101; 109; 101; 110; 116; 115; 32; 105;
   110; 32; 116; 104; 101; 32; 115; 116; 114; 105; 110; 103; 32; 105;
   32; 111; 102; 32; 116; 104; 101; 32; 105; 110; 112; 117; 116; 46].

Definition template_literal_113 : string :=
  "the number of odd elements in the string i of the input."%string.

Definition template_len_113 : Z := Zlength template_payload_113.

Fixpoint replace_i_payload_113 (tmpl digits : list Z) : list Z :=
  match tmpl with
  | [] => []
  | c :: rest =>
      if Z.eqb c 105
      then digits ++ replace_i_payload_113 rest digits
      else c :: replace_i_payload_113 rest digits
  end.

Fixpoint count_i_payload_113 (tmpl : list Z) : Z :=
  match tmpl with
  | [] => 0
  | c :: rest =>
      (if Z.eqb c 105 then 1 else 0) + count_i_payload_113 rest
  end.

Definition template_prefix_payload_113 (i : Z) (digits : list Z) : list Z :=
  replace_i_payload_113 (firstn (Z.to_nat i) template_payload_113) digits.

Definition template_fill_state_113
    (i : Z) (digits : list Z) (k : Z) (out_l : list Z) : Prop :=
  0 <= i <= template_len_113 /\
  out_l = template_prefix_payload_113 i digits /\
  k = Zlength out_l.

Definition odd_count_row_113 (row : list Z) : list Z :=
  c_string
    (replace_i_payload_113
       template_payload_113
       (decimal_digits_113 (odd_digit_count_row_113 row))).

Definition odd_count_rows_113 (rows : list (list Z)) : list (list Z) :=
  map odd_count_row_113 rows.

Definition odd_count_state_113
    (rows : list (list Z)) (i : Z) (output_rows : list (list Z)) : Prop :=
  0 <= i <= Zlength rows /\
  output_rows = odd_count_rows_113 (firstn (Z.to_nat i) rows).

Fixpoint odd_count_rows_heap_113
    (row_ptrs : list Z) (rows : list (list Z)) : Assertion :=
  match row_ptrs, rows with
  | p :: ps, row :: rs =>
      CharArray.full p (Zlength row) row ** odd_count_rows_heap_113 ps rs
  | _, _ => emp
  end.

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

Definition template_expanded_113 (digits : list Z) : list Z :=
  [116; 104; 101; 32; 110; 117; 109; 98; 101; 114; 32; 111; 102; 32;
   111; 100; 100; 32; 101; 108; 101; 109; 101; 110; 116; 115; 32] ++
  digits ++
  [110; 32; 116; 104; 101; 32; 115; 116; 114] ++
  digits ++
  [110; 103; 32] ++
  digits ++
  [32; 111; 102; 32; 116; 104; 101; 32] ++
  digits ++
  [110; 112; 117; 116; 46].

Definition template_expanded_ascii_113 (digits : list Z) : list ascii :=
  list_ascii_of_string "the number of odd elements " ++
  map ascii_of_z_113 digits ++
  list_ascii_of_string "n the str" ++
  map ascii_of_z_113 digits ++
  list_ascii_of_string "ng " ++
  map ascii_of_z_113 digits ++
  list_ascii_of_string " of the " ++
  map ascii_of_z_113 digits ++
  list_ascii_of_string "nput.".

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
