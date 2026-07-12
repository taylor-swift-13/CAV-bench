(* def do_algebra(operator, operand):
"""
Given two lists operator, and operand. The first list has basic algebra operations, and
the second list is a list of integers. Use the two given lists to build the algebric
expression and return the evaluation of this expression.

The basic algebra operations:
Addition ( + )
Subtraction ( - )
Multiplication ( * )
Floor division ( // )
Exponentiation ( ** )

Example:
operator['+', '*', '-']
array = [2, 3, 4, 5]
result = 2 + 3 * 4 - 5
=> result = 9

Note:
The length of operator list is equal to the length of operand list minus one.
Operand is a list of of non-negative integers.
Operator list has at least one operator, and operand list has at least two operands.

""" *)
(* 引入所需的Coq库 *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.


(* 此函数将字符形式的运算符解释为对应的二元整数运算。*)
Definition interp_op (op : ascii) : (Z -> Z -> Z) :=
  match op with
  | "+"%char => Z.add
  | "-"%char => Z.sub
  | "*"%char => Z.mul
  | "/"%char => Z.div
  | "^"%char => Z.pow
  | _ => fun _ _ => 0
  end.

Definition eval (ops : list ascii) (nums : list Z) : Z :=
  let prec := fun op =>
    match op with
    | "+"%char | "-"%char => 0%nat
    | "*"%char | "/"%char => 1%nat
    | "^"%char => 2%nat
    | _ => 0%nat
    end in
  let should_reduce := fun incoming top =>
    orb (Nat.ltb (prec incoming) (prec top))
        (andb (Nat.eqb (prec incoming) (prec top))
              (negb (incoming =? "^"%char)%char)) in
  let apply_top : (list Z * list ascii)%type -> (list Z * list ascii)%type :=
    fun st =>
      match st with
      | (rhs :: lhs :: values, op :: rest_ops) =>
          (interp_op op lhs rhs :: values, rest_ops)
      | _ => st
      end in
  let reduce_before : ascii -> (list Z * list ascii)%type -> (list Z * list ascii)%type :=
    fun incoming st =>
      Nat.iter (List.length (snd st))
        (fun st' =>
           match snd st' with
           | top :: _ => if should_reduce incoming top then apply_top st' else st'
           | [] => st'
           end)
        st in
  let push : (list Z * list ascii)%type -> (ascii * Z)%type -> (list Z * list ascii)%type :=
    fun st item =>
      let '(op, rhs) := item in
      let st' := reduce_before op st in
      (rhs :: fst st', op :: snd st') in
  let st := fold_left push (combine ops (tl nums)) ([hd 0 nums], []) in
  match fst (Nat.iter (List.length (snd st)) apply_top st) with
  | result :: _ => result
  | [] => 0
  end.

Definition do_algebra_impl (operators : string) (operands : list Z) : Z :=
  eval (list_ascii_of_string operators) operands.

(* 约束：
   - 操作符长度 = 操作数长度 - 1，且操作符至少1个、操作数至少2个
   - 操作数非负
   - 操作符仅限于 + - * / ^
*)
Definition problem_160_pre (operators : string) (operands : list Z) : Prop :=
  let ops := list_ascii_of_string operators in
  S (List.length ops) = List.length operands /\
  (1 <= List.length ops)%nat /\ (2 <= List.length operands)%nat /\
  Forall (fun z => 0 <= z) operands /\
  Forall (fun c => c = "+"%char \/ c = "-"%char \/ c = "*"%char \/ c = "/"%char \/ c = "^"%char) ops.

Definition problem_160_spec (operators : string) (operands : list Z) (result : Z) : Prop :=
  result = do_algebra_impl operators operands.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Program.Wf.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import SimpleC.StdLib.string_lib.

Import ListNotations.
Import naive_C_Rules.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope sac.

Definition ascii_of_z_160 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_ascii_list_160 (l : list ascii) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String c (string_of_ascii_list_160 rest)
  end.

Lemma list_ascii_of_string_string_of_ascii_list_160 :
  forall l,
    list_ascii_of_string (string_of_ascii_list_160 l) = l.
Proof.
  induction l as [| c rest IH]; simpl; [reflexivity |].
  rewrite IH.
  reflexivity.
Qed.

Definition row_payload_z_160 (row : list Z) : list Z :=
  firstn (Z.to_nat (Zlength row - 1)) row.

Definition operator_char_of_row_160 (row : list Z) : ascii :=
  match row_payload_z_160 row with
  | [43] => "+"%char
  | [45] => "-"%char
  | [42] => "*"%char
  | [47; 47] => "/"%char
  | [42; 42] => "^"%char
  | _ => " "%char
  end.

Definition operator_chars_160 (rows : list (list Z)) : list ascii :=
  map operator_char_of_row_160 rows.

Definition operator_string_160 (rows : list (list Z)) : string :=
  string_of_ascii_list_160 (operator_chars_160 rows).

Definition problem_160_pre_z (rows : list (list Z)) (operands : list Z) : Prop :=
  problem_160_pre (operator_string_160 rows) operands.

Definition problem_160_spec_z
    (rows : list (list Z)) (operands : list Z) (result : Z) : Prop :=
  problem_160_spec (operator_string_160 rows) operands result.

Definition Zpow_160 (base exp : Z) : Z :=
  Z.pow base exp.

Definition int_range_160 (z : Z) : Prop :=
  INT_MIN <= z <= INT_MAX.

Definition int_range_list_160 (l : list Z) : Prop :=
  Forall int_range_160 l.

Definition pow_prefix_safe_160 (base exp : Z) : Prop :=
  0 <= exp /\
  forall k, 0 <= k <= exp -> int_range_160 (Zpow_160 base k).

Definition operator_row_valid_160 (row : list Z) : Prop :=
  row = string_lib.c_string (row_payload_z_160 row) /\
  string_lib.valid_string (row_payload_z_160 row) /\
  string_lib.string_length (row_payload_z_160 row) < INT_MAX /\
  (row_payload_z_160 row = [43] \/
   row_payload_z_160 row = [45] \/
   row_payload_z_160 row = [42] \/
   row_payload_z_160 row = [47; 47] \/
   row_payload_z_160 row = [42; 42]).

Definition operator_payload_valid_160 (payload : list Z) : Prop :=
  string_lib.valid_string payload /\
  string_lib.string_length payload < INT_MAX /\
  (payload = [43] \/
   payload = [45] \/
   payload = [42] \/
   payload = [47; 47] \/
   payload = [42; 42]).

Definition operator_code_payload_160 (payload : list Z) : Z :=
  match payload with
  | [43] => 0
  | [45] => 1
  | [42] => 2
  | [47; 47] => 3
  | [42; 42] => 4
  | _ => 0
  end.

Definition operator_codes_160 (rows : list (list Z)) : list Z :=
  map (fun row => operator_code_payload_160 (row_payload_z_160 row)) rows.

Lemma Zlength_map_160 :
  forall {A B : Type} (f : A -> B) (l : list A),
    Zlength (map f l) = Zlength l.
Proof.
  intros A B f l.
  repeat rewrite Zlength_correct.
  rewrite map_length.
  reflexivity.
Qed.

Lemma Znth_map_160 :
  forall {A B : Type} (f : A -> B) l i da db,
    0 <= i < Zlength l ->
    Znth i (map f l) db = f (Znth i l da).
Proof.
  intros A B f l i da db Hi.
  unfold Znth.
  transitivity (nth (Z.to_nat i) (map f l) (f da)).
  - apply nth_indep.
    rewrite map_length.
    rewrite Zlength_correct in Hi.
    lia.
  - apply map_nth.
Qed.

Lemma operator_codes_prefix_snoc_160 :
  forall rows i,
    0 <= i < Zlength rows ->
    sublist 0 i (operator_codes_160 rows) ++
      operator_code_payload_160 (row_payload_z_160 (Znth i rows nil)) :: nil =
    sublist 0 (i + 1) (operator_codes_160 rows).
Proof.
  intros rows i Hi.
  rewrite (sublist_split 0 (i + 1) i (operator_codes_160 rows)) by
    (unfold operator_codes_160; try rewrite Zlength_map_160; lia).
  rewrite sublist_single with (d := 0) by
    (unfold operator_codes_160; try rewrite Zlength_map_160; lia).
  replace (Znth i (operator_codes_160 rows) 0) with
    (operator_code_payload_160 (row_payload_z_160 (Znth i rows nil))).
  2: {
    unfold operator_codes_160.
    rewrite (Znth_map_160 (fun row => operator_code_payload_160 (row_payload_z_160 row))
      rows i nil 0) by lia.
    reflexivity.
  }
  reflexivity.
Qed.

Definition is_addsub_code_160 (op : Z) : bool :=
  Z.eqb op 0 || Z.eqb op 1.

Definition is_muldiv_code_160 (op : Z) : bool :=
  Z.eqb op 2 || Z.eqb op 3.

Definition is_pow_code_160 (op : Z) : bool :=
  Z.eqb op 4.

Definition apply_code_160 (op lhs rhs : Z) : Z :=
  if Z.eqb op 0 then lhs + rhs
  else if Z.eqb op 1 then lhs - rhs
  else if Z.eqb op 2 then lhs * rhs
  else if Z.eqb op 3 then Z.quot lhs rhs
  else if Z.eqb op 4 then Zpow_160 lhs rhs
  else 0.

Fixpoint find_right_prefix_nat_160
    (fuel : nat) (p : Z -> bool) (ops : list Z) (lo : Z) : Z :=
  match fuel with
  | O => -1
  | S fuel' =>
      let prev := find_right_prefix_nat_160 fuel' p ops lo in
      let k := lo + Z.of_nat fuel' in
      if p (Znth k ops 0) then k else prev
  end.

Definition find_addsub_prefix_160 (ops : list Z) (lo i : Z) : Z :=
  find_right_prefix_nat_160 (Z.to_nat (i - lo)) is_addsub_code_160 ops lo.

Definition find_muldiv_prefix_160 (ops : list Z) (lo i : Z) : Z :=
  find_right_prefix_nat_160 (Z.to_nat (i - lo)) is_muldiv_code_160 ops lo.

Fixpoint find_pow_left_prefix_nat_160
    (fuel : nat) (ops : list Z) (lo : Z) : Z :=
  match fuel with
  | O => -1
  | S fuel' =>
      let prev := find_pow_left_prefix_nat_160 fuel' ops lo in
      let k := lo + Z.of_nat fuel' in
      if Z.eqb prev (-1)
      then if is_pow_code_160 (Znth k ops 0) then k else -1
      else prev
  end.

Definition find_pow_left_prefix_160 (ops : list Z) (lo i : Z) : Z :=
  find_pow_left_prefix_nat_160 (Z.to_nat (i - lo)) ops lo.

Lemma find_right_prefix_succ_160 :
  forall p ops lo i,
    lo <= i ->
    find_right_prefix_nat_160 (Z.to_nat (i + 1 - lo)) p ops lo =
    if p (Znth i ops 0)
    then i
    else find_right_prefix_nat_160 (Z.to_nat (i - lo)) p ops lo.
Proof.
  intros p ops lo i Hle.
  replace (i + 1 - lo) with (Z.succ (i - lo)) by lia.
  rewrite Z2Nat.inj_succ by lia.
  simpl.
  replace (lo + Z.of_nat (Z.to_nat (i - lo))) with i by lia.
  reflexivity.
Qed.

Lemma find_addsub_prefix_base_160 :
  forall ops lo,
    find_addsub_prefix_160 ops lo lo = -1.
Proof.
  intros. unfold find_addsub_prefix_160. replace (lo - lo) with 0 by lia. reflexivity.
Qed.

Lemma find_addsub_prefix_succ_hit_160 :
  forall ops lo i,
    lo <= i ->
    is_addsub_code_160 (Znth i ops 0) = true ->
    find_addsub_prefix_160 ops lo (i + 1) = i.
Proof.
  intros ops lo i Hle Hhit.
  unfold find_addsub_prefix_160.
  rewrite find_right_prefix_succ_160 by lia.
  rewrite Hhit. reflexivity.
Qed.

Lemma find_addsub_prefix_succ_miss_160 :
  forall ops lo i,
    lo <= i ->
    is_addsub_code_160 (Znth i ops 0) = false ->
    find_addsub_prefix_160 ops lo (i + 1) =
    find_addsub_prefix_160 ops lo i.
Proof.
  intros ops lo i Hle Hmiss.
  unfold find_addsub_prefix_160 at 1.
  rewrite find_right_prefix_succ_160 by lia.
  rewrite Hmiss. reflexivity.
Qed.

Lemma find_muldiv_prefix_base_160 :
  forall ops lo,
    find_muldiv_prefix_160 ops lo lo = -1.
Proof.
  intros. unfold find_muldiv_prefix_160. replace (lo - lo) with 0 by lia. reflexivity.
Qed.

Lemma find_muldiv_prefix_succ_hit_160 :
  forall ops lo i,
    lo <= i ->
    is_muldiv_code_160 (Znth i ops 0) = true ->
    find_muldiv_prefix_160 ops lo (i + 1) = i.
Proof.
  intros ops lo i Hle Hhit.
  unfold find_muldiv_prefix_160.
  rewrite find_right_prefix_succ_160 by lia.
  rewrite Hhit. reflexivity.
Qed.

Lemma find_muldiv_prefix_succ_miss_160 :
  forall ops lo i,
    lo <= i ->
    is_muldiv_code_160 (Znth i ops 0) = false ->
    find_muldiv_prefix_160 ops lo (i + 1) =
    find_muldiv_prefix_160 ops lo i.
Proof.
  intros ops lo i Hle Hmiss.
  unfold find_muldiv_prefix_160 at 1.
  rewrite find_right_prefix_succ_160 by lia.
  rewrite Hmiss. reflexivity.
Qed.

Lemma find_pow_left_prefix_succ_160 :
  forall ops lo i,
    lo <= i ->
    find_pow_left_prefix_160 ops lo (i + 1) =
    let prev := find_pow_left_prefix_160 ops lo i in
    if Z.eqb prev (-1)
    then if is_pow_code_160 (Znth i ops 0) then i else -1
    else prev.
Proof.
  intros ops lo i Hle.
  unfold find_pow_left_prefix_160.
  replace (i + 1 - lo) with (Z.succ (i - lo)) by lia.
  rewrite Z2Nat.inj_succ by lia.
  simpl.
  replace (lo + Z.of_nat (Z.to_nat (i - lo))) with i by lia.
  reflexivity.
Qed.

Lemma find_pow_left_prefix_base_160 :
  forall ops lo,
    find_pow_left_prefix_160 ops lo lo = -1.
Proof.
  intros. unfold find_pow_left_prefix_160. replace (lo - lo) with 0 by lia. reflexivity.
Qed.

Lemma find_pow_left_prefix_succ_first_160 :
  forall ops lo i,
    lo <= i ->
    find_pow_left_prefix_160 ops lo i = -1 ->
    is_pow_code_160 (Znth i ops 0) = true ->
    find_pow_left_prefix_160 ops lo (i + 1) = i.
Proof.
  intros ops lo i Hle Hprev Hhit.
  rewrite find_pow_left_prefix_succ_160 by lia.
  rewrite Hprev, Hhit. reflexivity.
Qed.

Lemma find_pow_left_prefix_succ_miss_160 :
  forall ops lo i,
    lo <= i ->
    find_pow_left_prefix_160 ops lo i = -1 ->
    is_pow_code_160 (Znth i ops 0) = false ->
    find_pow_left_prefix_160 ops lo (i + 1) = -1.
Proof.
  intros ops lo i Hle Hprev Hmiss.
  rewrite find_pow_left_prefix_succ_160 by lia.
  rewrite Hprev, Hmiss. reflexivity.
Qed.

Lemma find_pow_left_prefix_succ_keep_160 :
  forall ops lo i,
    lo <= i ->
    find_pow_left_prefix_160 ops lo i <> -1 ->
    find_pow_left_prefix_160 ops lo (i + 1) =
    find_pow_left_prefix_160 ops lo i.
Proof.
  intros ops lo i Hle Hprev.
  rewrite find_pow_left_prefix_succ_160 by lia.
  cbn zeta.
  destruct (Z.eqb (find_pow_left_prefix_160 ops lo i) (-1)) eqn:Heq.
  - apply Z.eqb_eq in Heq; contradiction.
  - reflexivity.
Qed.

Lemma find_right_prefix_nat_hit_160 :
  forall fuel p ops lo idx,
    idx = find_right_prefix_nat_160 fuel p ops lo ->
    0 <= idx ->
    p (Znth idx ops 0) = true.
Proof.
  induction fuel as [|fuel IH]; intros p ops lo idx Hidx Hnonneg; simpl in Hidx.
  - lia.
  - destruct (p (Znth (lo + Z.of_nat fuel) ops 0)) eqn:Hp.
    + subst idx. exact Hp.
    + eapply IH; eauto.
Qed.

Lemma find_right_prefix_nat_bound_160 :
  forall fuel p ops lo idx,
    idx = find_right_prefix_nat_160 fuel p ops lo ->
    0 <= idx ->
    lo <= idx < lo + Z.of_nat fuel.
Proof.
  induction fuel as [|fuel IH]; intros p ops lo idx Hidx Hnonneg; simpl in Hidx.
  - lia.
  - destruct (p (Znth (lo + Z.of_nat fuel) ops 0)) eqn:Hp.
    + subst idx. lia.
    + pose proof (IH p ops lo idx Hidx Hnonneg) as Hbound. lia.
Qed.

Lemma find_addsub_prefix_bound_160 :
  forall ops lo hi idx,
    idx = find_addsub_prefix_160 ops lo hi ->
    0 <= idx ->
    lo <= idx < hi.
Proof.
  intros ops lo hi idx Hfind Hidx.
  unfold find_addsub_prefix_160 in Hfind.
  pose proof (find_right_prefix_nat_bound_160 _ _ _ _ _ Hfind Hidx) as Hbound.
  assert (0 <= hi - lo).
  { destruct (Z_le_gt_dec 0 (hi - lo)); [lia|].
    assert (Z.to_nat (hi - lo) = 0%nat) by lia.
    rewrite H in Hbound; lia. }
  rewrite Z2Nat.id in Hbound by lia.
  lia.
Qed.

Lemma find_muldiv_prefix_bound_160 :
  forall ops lo hi idx,
    idx = find_muldiv_prefix_160 ops lo hi ->
    0 <= idx ->
    lo <= idx < hi.
Proof.
  intros ops lo hi idx Hfind Hidx.
  unfold find_muldiv_prefix_160 in Hfind.
  pose proof (find_right_prefix_nat_bound_160 _ _ _ _ _ Hfind Hidx) as Hbound.
  assert (0 <= hi - lo).
  { destruct (Z_le_gt_dec 0 (hi - lo)); [lia|].
    assert (Z.to_nat (hi - lo) = 0%nat) by lia.
    rewrite H in Hbound; lia. }
  rewrite Z2Nat.id in Hbound by lia.
  lia.
Qed.

Lemma find_pow_left_prefix_nat_bound_160 :
  forall fuel ops lo idx,
    idx = find_pow_left_prefix_nat_160 fuel ops lo ->
    0 <= idx ->
    lo <= idx < lo + Z.of_nat fuel.
Proof.
  induction fuel as [|fuel IH]; intros ops lo idx Hidx Hnonneg; simpl in Hidx.
  - lia.
  - destruct (Z.eqb (find_pow_left_prefix_nat_160 fuel ops lo) (-1)) eqn:Hprev.
    + destruct (is_pow_code_160 (Znth (lo + Z.of_nat fuel) ops 0)) eqn:Hpow.
      * subst idx. lia.
      * lia.
    + pose proof (IH ops lo idx Hidx Hnonneg) as Hbound. lia.
Qed.

Lemma find_pow_left_prefix_bound_160 :
  forall ops lo hi idx,
    idx = find_pow_left_prefix_160 ops lo hi ->
    0 <= idx ->
    lo <= idx < hi.
Proof.
  intros ops lo hi idx Hfind Hidx.
  unfold find_pow_left_prefix_160 in Hfind.
  pose proof (find_pow_left_prefix_nat_bound_160 _ _ _ _ Hfind Hidx) as Hbound.
  assert (0 <= hi - lo).
  { destruct (Z_le_gt_dec 0 (hi - lo)); [lia|].
    assert (Z.to_nat (hi - lo) = 0%nat) by lia.
    rewrite H in Hbound; lia. }
  rewrite Z2Nat.id in Hbound by lia.
  lia.
Qed.

Lemma find_pow_left_prefix_nat_hit_160 :
  forall fuel ops lo idx,
    idx = find_pow_left_prefix_nat_160 fuel ops lo ->
    0 <= idx ->
    is_pow_code_160 (Znth idx ops 0) = true.
Proof.
  induction fuel as [|fuel IH]; intros ops lo idx Hidx Hnonneg; simpl in Hidx.
  - lia.
  - destruct (Z.eqb (find_pow_left_prefix_nat_160 fuel ops lo) (-1)) eqn:Hprev.
    + destruct (is_pow_code_160 (Znth (lo + Z.of_nat fuel) ops 0)) eqn:Hpow.
      * subst idx. exact Hpow.
      * lia.
    + eapply IH; eauto.
Qed.

Lemma find_pow_left_prefix_hit_is_four_160 :
  forall ops lo hi idx,
    idx = find_pow_left_prefix_160 ops lo hi ->
    0 <= idx ->
    Znth idx ops 0 = 4.
Proof.
  intros ops lo hi idx Hfind Hidx.
  unfold find_pow_left_prefix_160 in Hfind.
  pose proof (find_pow_left_prefix_nat_hit_160 _ _ _ _ Hfind Hidx) as Hhit.
  unfold is_pow_code_160 in Hhit.
  apply Z.eqb_eq in Hhit.
  exact Hhit.
Qed.

Lemma find_addsub_prefix_nonzero_is_one_160 :
  forall ops lo hi idx,
    idx = find_addsub_prefix_160 ops lo hi ->
    0 <= idx ->
    Znth idx ops 0 <> 0 ->
    Znth idx ops 0 = 1.
Proof.
  intros ops lo hi idx Hfind Hidx Hnz.
  unfold find_addsub_prefix_160 in Hfind.
  pose proof (find_right_prefix_nat_hit_160 _ _ _ _ _ Hfind Hidx) as Hhit.
  unfold is_addsub_code_160 in Hhit.
  apply orb_true_iff in Hhit as [H0 | H1].
  - apply Z.eqb_eq in H0; lia.
  - apply Z.eqb_eq in H1; exact H1.
Qed.

Lemma find_muldiv_prefix_not_two_is_three_160 :
  forall ops lo hi idx,
    idx = find_muldiv_prefix_160 ops lo hi ->
    0 <= idx ->
    Znth idx ops 0 <> 2 ->
    Znth idx ops 0 = 3.
Proof.
  intros ops lo hi idx Hfind Hidx Hnz.
  unfold find_muldiv_prefix_160 in Hfind.
  pose proof (find_right_prefix_nat_hit_160 _ _ _ _ _ Hfind Hidx) as Hhit.
  unfold is_muldiv_code_160 in Hhit.
  apply orb_true_iff in Hhit as [H2 | H3].
  - apply Z.eqb_eq in H2; lia.
  - apply Z.eqb_eq in H3; exact H3.
Qed.

Fixpoint eval_range_fuel_160
    (fuel : nat) (ops nums : list Z) (lo hi : Z) : Z :=
  match fuel with
  | O => 0
  | S fuel' =>
      if Z.eqb lo hi then Znth lo nums 0
      else
        let idx := find_addsub_prefix_160 ops lo hi in
        if Z.geb idx 0 then
          apply_code_160 (Znth idx ops 0)
            (eval_range_fuel_160 fuel' ops nums lo idx)
            (eval_range_fuel_160 fuel' ops nums (idx + 1) hi)
        else
          let idx := find_muldiv_prefix_160 ops lo hi in
          if Z.geb idx 0 then
            apply_code_160 (Znth idx ops 0)
              (eval_range_fuel_160 fuel' ops nums lo idx)
              (eval_range_fuel_160 fuel' ops nums (idx + 1) hi)
          else
            let idx := find_pow_left_prefix_160 ops lo hi in
            if Z.geb idx 0 then
              apply_code_160 (Znth idx ops 0)
                (eval_range_fuel_160 fuel' ops nums lo idx)
                (eval_range_fuel_160 fuel' ops nums (idx + 1) hi)
            else 0
  end.

Definition eval_range_160 (ops nums : list Z) (lo hi : Z) : Z :=
  eval_range_fuel_160 (Z.to_nat (hi - lo + 1)) ops nums lo hi.

Lemma eval_range_base_160 :
  forall ops nums lo,
    eval_range_160 ops nums lo lo = Znth lo nums 0.
Proof.
  intros ops nums lo.
  unfold eval_range_160.
  replace (lo - lo + 1) with 1 by lia.
  change (Z.to_nat 1) with 1%nat.
  simpl. rewrite Z.eqb_refl.
  reflexivity.
Qed.

Lemma eval_range_no_operator_160 :
  forall ops nums lo hi,
    lo < hi ->
    find_addsub_prefix_160 ops lo hi < 0 ->
    find_muldiv_prefix_160 ops lo hi < 0 ->
    find_pow_left_prefix_160 ops lo hi < 0 ->
    eval_range_160 ops nums lo hi = 0.
Proof.
  intros ops nums lo hi Hlt Hadd Hmul Hpow.
  unfold eval_range_160.
  assert (0 < hi - lo + 1) by lia.
  destruct (Z.to_nat (hi - lo + 1)) eqn:Hfuel; [lia |].
  simpl.
  replace (Z.eqb lo hi) with false by (symmetry; apply Z.eqb_neq; lia).
  destruct (Z.geb (find_addsub_prefix_160 ops lo hi) 0) eqn:Hadd_ge.
  { apply Z.geb_le in Hadd_ge; lia. }
  destruct (Z.geb (find_muldiv_prefix_160 ops lo hi) 0) eqn:Hmul_ge.
  { apply Z.geb_le in Hmul_ge; lia. }
  destruct (Z.geb (find_pow_left_prefix_160 ops lo hi) 0) eqn:Hpow_ge.
  { apply Z.geb_le in Hpow_ge; lia. }
  reflexivity.
Qed.

Lemma sub_fuel_left_160 :
  forall lo hi idx need,
    lo <= idx < hi ->
    Z.to_nat (hi - lo + 1) = S need ->
    (Z.to_nat (idx - lo + 1) <= need)%nat.
Proof.
  intros lo hi idx need Hbound Hneed.
  replace (hi - lo + 1) with (Z.succ (hi - lo)) in Hneed by lia.
  rewrite Z2Nat.inj_succ in Hneed by lia.
  inversion Hneed; subst need.
  apply Z2Nat.inj_le; lia.
Qed.

Lemma sub_fuel_right_160 :
  forall lo hi idx need,
    lo <= idx < hi ->
    Z.to_nat (hi - lo + 1) = S need ->
    (Z.to_nat (hi - (idx + 1) + 1) <= need)%nat.
Proof.
  intros lo hi idx need Hbound Hneed.
  replace (hi - lo + 1) with (Z.succ (hi - lo)) in Hneed by lia.
  rewrite Z2Nat.inj_succ in Hneed by lia.
  inversion Hneed; subst need.
  apply Z2Nat.inj_le; lia.
Qed.

Lemma sub_fuel_left_lt_160 :
  forall lo hi idx,
    lo <= idx < hi ->
    (Z.to_nat (idx - lo + 1) < Z.to_nat (hi - lo + 1))%nat.
Proof.
  intros lo hi idx Hbound.
  apply Z2Nat.inj_lt; lia.
Qed.

Lemma sub_fuel_right_lt_160 :
  forall lo hi idx,
    lo <= idx < hi ->
    (Z.to_nat (hi - (idx + 1) + 1) < Z.to_nat (hi - lo + 1))%nat.
Proof.
  intros lo hi idx Hbound.
  apply Z2Nat.inj_lt; lia.
Qed.

Fixpoint eval_range_safe_fuel_160
    (fuel : nat) (ops nums : list Z) (lo hi : Z) : Prop :=
  match fuel with
  | O => False
  | S fuel' =>
      0 <= lo <= hi /\
      hi < Zlength nums /\
      hi <= Zlength ops /\
      (if Z.eqb lo hi then int_range_160 (Znth lo nums 0)
       else
         let idx := find_addsub_prefix_160 ops lo hi in
         if Z.geb idx 0 then
           eval_range_safe_fuel_160 fuel' ops nums lo idx /\
           eval_range_safe_fuel_160 fuel' ops nums (idx + 1) hi /\
           int_range_160
             (apply_code_160 (Znth idx ops 0)
               (eval_range_160 ops nums lo idx)
               (eval_range_160 ops nums (idx + 1) hi))
         else
           let idx := find_muldiv_prefix_160 ops lo hi in
           if Z.geb idx 0 then
             eval_range_safe_fuel_160 fuel' ops nums lo idx /\
             eval_range_safe_fuel_160 fuel' ops nums (idx + 1) hi /\
             (Znth idx ops 0 = 3 ->
                eval_range_160 ops nums (idx + 1) hi <> 0) /\
             (Znth idx ops 0 = 3 ->
                eval_range_160 ops nums lo idx <> INT_MIN \/
                eval_range_160 ops nums (idx + 1) hi <> -1) /\
             int_range_160
               (apply_code_160 (Znth idx ops 0)
                 (eval_range_160 ops nums lo idx)
                 (eval_range_160 ops nums (idx + 1) hi))
           else
             let idx := find_pow_left_prefix_160 ops lo hi in
             if Z.geb idx 0 then
               eval_range_safe_fuel_160 fuel' ops nums lo idx /\
               eval_range_safe_fuel_160 fuel' ops nums (idx + 1) hi /\
               0 <= eval_range_160 ops nums (idx + 1) hi /\
               eval_range_160 ops nums (idx + 1) hi < INT_MAX /\
               pow_prefix_safe_160
                 (eval_range_160 ops nums lo idx)
                 (eval_range_160 ops nums (idx + 1) hi) /\
               int_range_160
                 (apply_code_160 (Znth idx ops 0)
                   (eval_range_160 ops nums lo idx)
                   (eval_range_160 ops nums (idx + 1) hi))
             else int_range_160 0)
  end.

Definition eval_range_safe_160 (ops nums : list Z) (lo hi : Z) : Prop :=
  eval_range_safe_fuel_160 (Z.to_nat (hi - lo + 1)) ops nums lo hi.

Lemma eval_range_safe_fuel_shrink_160 :
  forall source target ops nums lo hi,
    eval_range_safe_fuel_160 source ops nums lo hi ->
    (Z.to_nat (hi - lo + 1) <= target)%nat ->
    (target <= source)%nat ->
    eval_range_safe_fuel_160 target ops nums lo hi.
Proof.
  induction source as [source IH] using lt_wf_ind.
  intros target ops nums lo hi Hsafe Htarget Hle.
  destruct source as [|source']; [contradiction|].
  simpl in Hsafe.
  destruct Hsafe as [Hlohi [Hnum [Hops Hsafe]]].
  assert (Hexact_pos : Z.to_nat (hi - lo + 1) <> O).
  {
    intro Hz.
    apply (f_equal Z.of_nat) in Hz.
    rewrite Nat2Z.inj_0 in Hz.
    rewrite Z2Nat.id in Hz by lia.
    lia.
  }
  destruct target as [|target']; [lia|].
  simpl.
  split; [exact Hlohi|].
  split; [exact Hnum|].
  split; [exact Hops|].
  destruct (Z.eqb lo hi) eqn:Hbase; [exact Hsafe|].
  assert (Hlt : lo < hi) by (apply Z.eqb_neq in Hbase; lia).
  destruct (Z.geb (find_addsub_prefix_160 ops lo hi) 0) eqn:Hadd_ge.
  - destruct Hsafe as [Hleft [Hright Hrange]].
    pose proof Hadd_ge as Hadd_nonneg.
    apply Z.geb_le in Hadd_nonneg.
    pose proof (find_addsub_prefix_bound_160 ops lo hi
      (find_addsub_prefix_160 ops lo hi) eq_refl Hadd_nonneg) as Hbound.
    split.
    + eapply (IH source'); [lia | exact Hleft | | lia].
      pose proof (sub_fuel_left_lt_160 lo hi
        (find_addsub_prefix_160 ops lo hi) Hbound) as Hsub.
      lia.
    + split.
      * eapply (IH source'); [lia | exact Hright | | lia].
      pose proof (sub_fuel_right_lt_160 lo hi
        (find_addsub_prefix_160 ops lo hi) Hbound) as Hsub.
      lia.
      * exact Hrange.
  - destruct (Z.geb (find_muldiv_prefix_160 ops lo hi) 0) eqn:Hmul_ge.
    + destruct Hsafe as [Hleft [Hright [Hdiv [Hover Hrange]]]].
      pose proof Hmul_ge as Hmul_nonneg.
      apply Z.geb_le in Hmul_nonneg.
      pose proof (find_muldiv_prefix_bound_160 ops lo hi
        (find_muldiv_prefix_160 ops lo hi) eq_refl Hmul_nonneg) as Hbound.
      split.
      * eapply (IH source'); [lia | exact Hleft | | lia].
        pose proof (sub_fuel_left_lt_160 lo hi
          (find_muldiv_prefix_160 ops lo hi) Hbound) as Hsub.
        lia.
      * split.
        -- eapply (IH source'); [lia | exact Hright | | lia].
        pose proof (sub_fuel_right_lt_160 lo hi
          (find_muldiv_prefix_160 ops lo hi) Hbound) as Hsub.
        lia.
        -- split; [exact Hdiv|].
           split; [exact Hover|exact Hrange].
    + destruct (Z.geb (find_pow_left_prefix_160 ops lo hi) 0) eqn:Hpow_ge.
      * destruct Hsafe as [Hleft [Hright [Hexp_nonneg [Hexp_bound [Hpow Hrange]]]]].
        pose proof Hpow_ge as Hpow_nonneg.
        apply Z.geb_le in Hpow_nonneg.
        pose proof (find_pow_left_prefix_bound_160 ops lo hi
          (find_pow_left_prefix_160 ops lo hi) eq_refl Hpow_nonneg) as Hbound.
        split.
        -- eapply (IH source'); [lia | exact Hleft | | lia].
           pose proof (sub_fuel_left_lt_160 lo hi
             (find_pow_left_prefix_160 ops lo hi) Hbound) as Hsub.
           lia.
        -- split.
           ++ eapply (IH source'); [lia | exact Hright | | lia].
           pose proof (sub_fuel_right_lt_160 lo hi
             (find_pow_left_prefix_160 ops lo hi) Hbound) as Hsub.
           lia.
           ++ split; [exact Hexp_nonneg|].
              split; [exact Hexp_bound|].
              split; [exact Hpow|exact Hrange].
      * exact Hsafe.
Qed.

Lemma eval_range_safe_addsub_left_160 :
  forall ops nums lo hi idx,
    lo < hi ->
    0 <= idx ->
    idx = find_addsub_prefix_160 ops lo hi ->
    eval_range_safe_160 ops nums lo hi ->
    eval_range_safe_160 ops nums lo idx.
Proof.
  intros ops nums lo hi idx Hlt Hidx Hfind Hsafe.
  unfold eval_range_safe_160 in *.
  assert (0 < hi - lo + 1) by lia.
  destruct (Z.to_nat (hi - lo + 1)) eqn:Hfuel; [lia|].
  simpl in Hsafe.
  destruct Hsafe as [_ [_ [_ Hsafe]]].
  replace (Z.eqb lo hi) with false in Hsafe by (symmetry; apply Z.eqb_neq; lia).
  rewrite <- Hfind in Hsafe.
  replace (Z.geb idx 0) with true in Hsafe by (symmetry; apply Z.geb_le; lia).
  destruct Hsafe as [Hleft _].
  pose proof (find_addsub_prefix_bound_160 ops lo hi idx Hfind Hidx) as Hbound.
  eapply eval_range_safe_fuel_shrink_160; [exact Hleft| |].
  - lia.
  - eapply sub_fuel_left_160; [exact Hbound|exact Hfuel].
Qed.

Lemma eval_range_safe_addsub_right_160 :
  forall ops nums lo hi idx,
    lo < hi ->
    0 <= idx ->
    idx = find_addsub_prefix_160 ops lo hi ->
    eval_range_safe_160 ops nums lo hi ->
    eval_range_safe_160 ops nums (idx + 1) hi.
Proof.
  intros ops nums lo hi idx Hlt Hidx Hfind Hsafe.
  unfold eval_range_safe_160 in *.
  assert (0 < hi - lo + 1) by lia.
  destruct (Z.to_nat (hi - lo + 1)) eqn:Hfuel; [lia|].
  simpl in Hsafe.
  destruct Hsafe as [_ [_ [_ Hsafe]]].
  replace (Z.eqb lo hi) with false in Hsafe by (symmetry; apply Z.eqb_neq; lia).
  rewrite <- Hfind in Hsafe.
  replace (Z.geb idx 0) with true in Hsafe by (symmetry; apply Z.geb_le; lia).
  destruct Hsafe as [_ [Hright _]].
  pose proof (find_addsub_prefix_bound_160 ops lo hi idx Hfind Hidx) as Hbound.
  eapply eval_range_safe_fuel_shrink_160; [exact Hright| |].
  - lia.
  - eapply sub_fuel_right_160; [exact Hbound|exact Hfuel].
Qed.

Lemma eval_range_safe_muldiv_left_160 :
  forall ops nums lo hi idx,
    lo < hi ->
    0 <= idx ->
    find_addsub_prefix_160 ops lo hi < 0 ->
    idx = find_muldiv_prefix_160 ops lo hi ->
    eval_range_safe_160 ops nums lo hi ->
    eval_range_safe_160 ops nums lo idx.
Proof.
  intros ops nums lo hi idx Hlt Hidx Hadd Hfind Hsafe.
  unfold eval_range_safe_160 in *.
  assert (0 < hi - lo + 1) by lia.
  destruct (Z.to_nat (hi - lo + 1)) eqn:Hfuel; [lia|].
  simpl in Hsafe.
  destruct Hsafe as [_ [_ [_ Hsafe]]].
  replace (Z.eqb lo hi) with false in Hsafe by (symmetry; apply Z.eqb_neq; lia).
  destruct (Z.geb (find_addsub_prefix_160 ops lo hi) 0) eqn:Hadd_ge.
  { apply Z.geb_le in Hadd_ge; lia. }
  rewrite <- Hfind in Hsafe.
  replace (Z.geb idx 0) with true in Hsafe by (symmetry; apply Z.geb_le; lia).
  destruct Hsafe as [Hleft _].
  pose proof (find_muldiv_prefix_bound_160 ops lo hi idx Hfind Hidx) as Hbound.
  eapply eval_range_safe_fuel_shrink_160; [exact Hleft| |].
  - lia.
  - eapply sub_fuel_left_160; [exact Hbound|exact Hfuel].
Qed.

Lemma eval_range_safe_muldiv_right_160 :
  forall ops nums lo hi idx,
    lo < hi ->
    0 <= idx ->
    find_addsub_prefix_160 ops lo hi < 0 ->
    idx = find_muldiv_prefix_160 ops lo hi ->
    eval_range_safe_160 ops nums lo hi ->
    eval_range_safe_160 ops nums (idx + 1) hi.
Proof.
  intros ops nums lo hi idx Hlt Hidx Hadd Hfind Hsafe.
  unfold eval_range_safe_160 in *.
  assert (0 < hi - lo + 1) by lia.
  destruct (Z.to_nat (hi - lo + 1)) eqn:Hfuel; [lia|].
  simpl in Hsafe.
  destruct Hsafe as [_ [_ [_ Hsafe]]].
  replace (Z.eqb lo hi) with false in Hsafe by (symmetry; apply Z.eqb_neq; lia).
  destruct (Z.geb (find_addsub_prefix_160 ops lo hi) 0) eqn:Hadd_ge.
  { apply Z.geb_le in Hadd_ge; lia. }
  rewrite <- Hfind in Hsafe.
  replace (Z.geb idx 0) with true in Hsafe by (symmetry; apply Z.geb_le; lia).
  destruct Hsafe as [_ [Hright _]].
  pose proof (find_muldiv_prefix_bound_160 ops lo hi idx Hfind Hidx) as Hbound.
  eapply eval_range_safe_fuel_shrink_160; [exact Hright| |].
  - lia.
  - eapply sub_fuel_right_160; [exact Hbound|exact Hfuel].
Qed.

Lemma eval_range_safe_pow_left_160 :
  forall ops nums lo hi idx,
    lo < hi ->
    0 <= idx ->
    find_addsub_prefix_160 ops lo hi < 0 ->
    find_muldiv_prefix_160 ops lo hi < 0 ->
    idx = find_pow_left_prefix_160 ops lo hi ->
    eval_range_safe_160 ops nums lo hi ->
    eval_range_safe_160 ops nums lo idx.
Proof.
  intros ops nums lo hi idx Hlt Hidx Hadd Hmul Hfind Hsafe.
  unfold eval_range_safe_160 in *.
  assert (0 < hi - lo + 1) by lia.
  destruct (Z.to_nat (hi - lo + 1)) eqn:Hfuel; [lia|].
  simpl in Hsafe.
  destruct Hsafe as [_ [_ [_ Hsafe]]].
  replace (Z.eqb lo hi) with false in Hsafe by (symmetry; apply Z.eqb_neq; lia).
  destruct (Z.geb (find_addsub_prefix_160 ops lo hi) 0) eqn:Hadd_ge.
  { apply Z.geb_le in Hadd_ge; lia. }
  destruct (Z.geb (find_muldiv_prefix_160 ops lo hi) 0) eqn:Hmul_ge.
  { apply Z.geb_le in Hmul_ge; lia. }
  rewrite <- Hfind in Hsafe.
  replace (Z.geb idx 0) with true in Hsafe by (symmetry; apply Z.geb_le; lia).
  destruct Hsafe as [Hleft _].
  pose proof (find_pow_left_prefix_bound_160 ops lo hi idx Hfind Hidx) as Hbound.
  eapply eval_range_safe_fuel_shrink_160; [exact Hleft| |].
  - lia.
  - eapply sub_fuel_left_160; [exact Hbound|exact Hfuel].
Qed.

Lemma eval_range_safe_pow_right_160 :
  forall ops nums lo hi idx,
    lo < hi ->
    0 <= idx ->
    find_addsub_prefix_160 ops lo hi < 0 ->
    find_muldiv_prefix_160 ops lo hi < 0 ->
    idx = find_pow_left_prefix_160 ops lo hi ->
    eval_range_safe_160 ops nums lo hi ->
    eval_range_safe_160 ops nums (idx + 1) hi.
Proof.
  intros ops nums lo hi idx Hlt Hidx Hadd Hmul Hfind Hsafe.
  unfold eval_range_safe_160 in *.
  assert (0 < hi - lo + 1) by lia.
  destruct (Z.to_nat (hi - lo + 1)) eqn:Hfuel; [lia|].
  simpl in Hsafe.
  destruct Hsafe as [_ [_ [_ Hsafe]]].
  replace (Z.eqb lo hi) with false in Hsafe by (symmetry; apply Z.eqb_neq; lia).
  destruct (Z.geb (find_addsub_prefix_160 ops lo hi) 0) eqn:Hadd_ge.
  { apply Z.geb_le in Hadd_ge; lia. }
  destruct (Z.geb (find_muldiv_prefix_160 ops lo hi) 0) eqn:Hmul_ge.
  { apply Z.geb_le in Hmul_ge; lia. }
  rewrite <- Hfind in Hsafe.
  replace (Z.geb idx 0) with true in Hsafe by (symmetry; apply Z.geb_le; lia).
  destruct Hsafe as [_ [Hright _]].
  pose proof (find_pow_left_prefix_bound_160 ops lo hi idx Hfind Hidx) as Hbound.
  eapply eval_range_safe_fuel_shrink_160; [exact Hright| |].
  - lia.
  - eapply sub_fuel_right_160; [exact Hbound|exact Hfuel].
Qed.

Lemma eval_range_fuel_safe_enough_gen_160 :
  forall fuel safe_fuel ops nums lo hi,
    eval_range_safe_fuel_160 safe_fuel ops nums lo hi ->
    (Z.to_nat (hi - lo + 1) <= fuel)%nat ->
    (Z.to_nat (hi - lo + 1) <= safe_fuel)%nat ->
    eval_range_fuel_160 fuel ops nums lo hi =
    eval_range_160 ops nums lo hi.
Proof.
  induction fuel as [fuel IH] using lt_wf_ind.
  intros safe_fuel ops nums lo hi Hsafe Hfuel Hsafe_fuel.
  unfold eval_range_160.
  remember (Z.to_nat (hi - lo + 1)) as exact eqn:Hexact.
  destruct safe_fuel as [|safe_fuel'].
  { contradiction. }
  simpl in Hsafe.
  destruct Hsafe as [Hlohi [Hnum [Hops Hsafe]]].
  assert (Hexact_pos : exact <> O).
  {
    subst exact.
    intro Hz.
    apply (f_equal Z.of_nat) in Hz.
    rewrite Nat2Z.inj_0 in Hz.
    rewrite Z2Nat.id in Hz by lia.
    lia.
  }
  destruct fuel as [|fuel'].
  { lia. }
  destruct exact as [|exact']; [contradiction|].
  simpl.
  destruct (Z.eqb lo hi) eqn:Hbase; [reflexivity|].
  assert (Hlt : lo < hi) by (apply Z.eqb_neq in Hbase; lia).
  destruct (Z.geb (find_addsub_prefix_160 ops lo hi) 0) eqn:Hadd_ge.
  - destruct Hsafe as [Hleft [Hright _]].
    pose proof Hadd_ge as Hadd_nonneg.
    apply Z.geb_le in Hadd_nonneg.
    pose proof (find_addsub_prefix_bound_160 ops lo hi
      (find_addsub_prefix_160 ops lo hi) eq_refl Hadd_nonneg) as Hbound.
    rewrite (IH fuel' ltac:(lia) safe_fuel' ops nums lo
      (find_addsub_prefix_160 ops lo hi) Hleft).
    2: {
      eapply Nat.le_trans.
      - eapply sub_fuel_left_160; eauto.
      - lia.
    }
    2: {
      eapply Nat.le_trans.
      - eapply sub_fuel_left_160; eauto.
      - lia.
    }
    rewrite (IH fuel' ltac:(lia) safe_fuel' ops nums
      (find_addsub_prefix_160 ops lo hi + 1) hi Hright).
    2: {
      eapply Nat.le_trans.
      - eapply sub_fuel_right_160; eauto.
      - lia.
    }
    2: {
      eapply Nat.le_trans.
      - eapply sub_fuel_right_160; eauto.
      - lia.
    }
    rewrite (IH exact' ltac:(lia) safe_fuel' ops nums lo
      (find_addsub_prefix_160 ops lo hi) Hleft).
    2: { eapply sub_fuel_left_160; eauto. }
    2: {
      eapply Nat.le_trans.
      - eapply sub_fuel_left_160; eauto.
      - lia.
    }
    rewrite (IH exact' ltac:(lia) safe_fuel' ops nums
      (find_addsub_prefix_160 ops lo hi + 1) hi Hright).
    2: { eapply sub_fuel_right_160; eauto. }
    2: {
      eapply Nat.le_trans.
      - eapply sub_fuel_right_160; eauto.
      - lia.
    }
    reflexivity.
  - destruct (Z.geb (find_muldiv_prefix_160 ops lo hi) 0) eqn:Hmul_ge.
    + destruct Hsafe as [Hleft [Hright _]].
      pose proof Hmul_ge as Hmul_nonneg.
      apply Z.geb_le in Hmul_nonneg.
      pose proof (find_muldiv_prefix_bound_160 ops lo hi
        (find_muldiv_prefix_160 ops lo hi) eq_refl Hmul_nonneg) as Hbound.
      rewrite (IH fuel' ltac:(lia) safe_fuel' ops nums lo
        (find_muldiv_prefix_160 ops lo hi) Hleft).
      2: {
        eapply Nat.le_trans.
        - eapply sub_fuel_left_160; eauto.
        - lia.
      }
      2: {
        eapply Nat.le_trans.
        - eapply sub_fuel_left_160; eauto.
        - lia.
      }
      rewrite (IH fuel' ltac:(lia) safe_fuel' ops nums
        (find_muldiv_prefix_160 ops lo hi + 1) hi Hright).
      2: {
        eapply Nat.le_trans.
        - eapply sub_fuel_right_160; eauto.
        - lia.
      }
      2: {
        eapply Nat.le_trans.
        - eapply sub_fuel_right_160; eauto.
        - lia.
      }
      rewrite (IH exact' ltac:(lia) safe_fuel' ops nums lo
        (find_muldiv_prefix_160 ops lo hi) Hleft).
      2: { eapply sub_fuel_left_160; eauto. }
      2: {
        eapply Nat.le_trans.
        - eapply sub_fuel_left_160; eauto.
        - lia.
      }
      rewrite (IH exact' ltac:(lia) safe_fuel' ops nums
        (find_muldiv_prefix_160 ops lo hi + 1) hi Hright).
      2: { eapply sub_fuel_right_160; eauto. }
      2: {
        eapply Nat.le_trans.
        - eapply sub_fuel_right_160; eauto.
        - lia.
      }
      reflexivity.
    + destruct (Z.geb (find_pow_left_prefix_160 ops lo hi) 0) eqn:Hpow_ge.
      * destruct Hsafe as [Hleft [Hright _]].
        pose proof Hpow_ge as Hpow_nonneg.
        apply Z.geb_le in Hpow_nonneg.
        pose proof (find_pow_left_prefix_bound_160 ops lo hi
          (find_pow_left_prefix_160 ops lo hi) eq_refl Hpow_nonneg) as Hbound.
        rewrite (IH fuel' ltac:(lia) safe_fuel' ops nums lo
          (find_pow_left_prefix_160 ops lo hi) Hleft).
        2: {
          eapply Nat.le_trans.
          - eapply sub_fuel_left_160; eauto.
          - lia.
        }
        2: {
          eapply Nat.le_trans.
          - eapply sub_fuel_left_160; eauto.
          - lia.
        }
        rewrite (IH fuel' ltac:(lia) safe_fuel' ops nums
          (find_pow_left_prefix_160 ops lo hi + 1) hi Hright).
        2: {
          eapply Nat.le_trans.
          - eapply sub_fuel_right_160; eauto.
          - lia.
        }
        2: {
          eapply Nat.le_trans.
          - eapply sub_fuel_right_160; eauto.
          - lia.
        }
        rewrite (IH exact' ltac:(lia) safe_fuel' ops nums lo
          (find_pow_left_prefix_160 ops lo hi) Hleft).
        2: { eapply sub_fuel_left_160; eauto. }
        2: {
          eapply Nat.le_trans.
          - eapply sub_fuel_left_160; eauto.
          - lia.
        }
        rewrite (IH exact' ltac:(lia) safe_fuel' ops nums
          (find_pow_left_prefix_160 ops lo hi + 1) hi Hright).
        2: { eapply sub_fuel_right_160; eauto. }
        2: {
          eapply Nat.le_trans.
          - eapply sub_fuel_right_160; eauto.
          - lia.
        }
        reflexivity.
      * reflexivity.
Qed.

Lemma eval_range_addsub_unfold_160 :
  forall ops nums lo hi idx,
    lo < hi ->
    0 <= idx ->
    idx = find_addsub_prefix_160 ops lo hi ->
    eval_range_safe_160 ops nums lo hi ->
    eval_range_160 ops nums lo hi =
    apply_code_160 (Znth idx ops 0)
      (eval_range_160 ops nums lo idx)
      (eval_range_160 ops nums (idx + 1) hi).
Proof.
  intros ops nums lo hi idx Hlt Hidx Hfind Hsafe.
  unfold eval_range_160 at 1.
  assert (0 < hi - lo + 1) by lia.
  destruct (Z.to_nat (hi - lo + 1)) eqn:Hfuel; [lia |].
  simpl.
  replace (Z.eqb lo hi) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite <- Hfind.
  replace (Z.geb idx 0) with true by (symmetry; apply Z.geb_le; lia).
  unfold eval_range_safe_160 in Hsafe.
  rewrite Hfuel in Hsafe.
  simpl in Hsafe.
  destruct Hsafe as [_ [_ [_ Hsafe]]].
  replace (Z.eqb lo hi) with false in Hsafe by (symmetry; apply Z.eqb_neq; lia).
  rewrite <- Hfind in Hsafe.
  replace (Z.geb idx 0) with true in Hsafe by (symmetry; apply Z.geb_le; lia).
  destruct Hsafe as [Hleft [Hright _]].
  pose proof (find_addsub_prefix_bound_160 ops lo hi idx Hfind Hidx) as Hbound.
  rewrite (eval_range_fuel_safe_enough_gen_160 n n ops nums lo idx Hleft).
  2: { eapply sub_fuel_left_160; eauto. }
  2: { eapply sub_fuel_left_160; eauto. }
  rewrite (eval_range_fuel_safe_enough_gen_160 n n ops nums (idx + 1) hi Hright).
  2: { eapply sub_fuel_right_160; eauto. }
  2: { eapply sub_fuel_right_160; eauto. }
  reflexivity.
Qed.

Lemma eval_range_muldiv_unfold_160 :
  forall ops nums lo hi idx,
    lo < hi ->
    0 <= idx ->
    find_addsub_prefix_160 ops lo hi < 0 ->
    idx = find_muldiv_prefix_160 ops lo hi ->
    eval_range_safe_160 ops nums lo hi ->
    eval_range_160 ops nums lo hi =
    apply_code_160 (Znth idx ops 0)
      (eval_range_160 ops nums lo idx)
      (eval_range_160 ops nums (idx + 1) hi).
Proof.
  intros ops nums lo hi idx Hlt Hidx Hadd Hfind Hsafe.
  unfold eval_range_160 at 1.
  assert (0 < hi - lo + 1) by lia.
  destruct (Z.to_nat (hi - lo + 1)) eqn:Hfuel; [lia |].
  simpl.
  replace (Z.eqb lo hi) with false by (symmetry; apply Z.eqb_neq; lia).
  destruct (Z.geb (find_addsub_prefix_160 ops lo hi) 0) eqn:Hadd_ge.
  { apply Z.geb_le in Hadd_ge; lia. }
  rewrite <- Hfind.
  replace (Z.geb idx 0) with true by (symmetry; apply Z.geb_le; lia).
  unfold eval_range_safe_160 in Hsafe.
  rewrite Hfuel in Hsafe.
  simpl in Hsafe.
  destruct Hsafe as [_ [_ [_ Hsafe]]].
  replace (Z.eqb lo hi) with false in Hsafe by (symmetry; apply Z.eqb_neq; lia).
  destruct (Z.geb (find_addsub_prefix_160 ops lo hi) 0) eqn:Hadd_ge2.
  { apply Z.geb_le in Hadd_ge2; lia. }
  rewrite <- Hfind in Hsafe.
  replace (Z.geb idx 0) with true in Hsafe by (symmetry; apply Z.geb_le; lia).
  destruct Hsafe as [Hleft [Hright _]].
  pose proof (find_muldiv_prefix_bound_160 ops lo hi idx Hfind Hidx) as Hbound.
  rewrite (eval_range_fuel_safe_enough_gen_160 n n ops nums lo idx Hleft).
  2: { eapply sub_fuel_left_160; eauto. }
  2: { eapply sub_fuel_left_160; eauto. }
  rewrite (eval_range_fuel_safe_enough_gen_160 n n ops nums (idx + 1) hi Hright).
  2: { eapply sub_fuel_right_160; eauto. }
  2: { eapply sub_fuel_right_160; eauto. }
  reflexivity.
Qed.

Lemma eval_range_pow_unfold_160 :
  forall ops nums lo hi idx,
    lo < hi ->
    0 <= idx ->
    find_addsub_prefix_160 ops lo hi < 0 ->
    find_muldiv_prefix_160 ops lo hi < 0 ->
    idx = find_pow_left_prefix_160 ops lo hi ->
    eval_range_safe_160 ops nums lo hi ->
    eval_range_160 ops nums lo hi =
    apply_code_160 (Znth idx ops 0)
      (eval_range_160 ops nums lo idx)
      (eval_range_160 ops nums (idx + 1) hi).
Proof.
  intros ops nums lo hi idx Hlt Hidx Hadd Hmul Hfind Hsafe.
  unfold eval_range_160 at 1.
  assert (0 < hi - lo + 1) by lia.
  destruct (Z.to_nat (hi - lo + 1)) eqn:Hfuel; [lia |].
  simpl.
  replace (Z.eqb lo hi) with false by (symmetry; apply Z.eqb_neq; lia).
  destruct (Z.geb (find_addsub_prefix_160 ops lo hi) 0) eqn:Hadd_ge.
  { apply Z.geb_le in Hadd_ge; lia. }
  destruct (Z.geb (find_muldiv_prefix_160 ops lo hi) 0) eqn:Hmul_ge.
  { apply Z.geb_le in Hmul_ge; lia. }
  rewrite <- Hfind.
  replace (Z.geb idx 0) with true by (symmetry; apply Z.geb_le; lia).
  unfold eval_range_safe_160 in Hsafe.
  rewrite Hfuel in Hsafe.
  simpl in Hsafe.
  destruct Hsafe as [_ [_ [_ Hsafe]]].
  replace (Z.eqb lo hi) with false in Hsafe by (symmetry; apply Z.eqb_neq; lia).
  destruct (Z.geb (find_addsub_prefix_160 ops lo hi) 0) eqn:Hadd_ge2.
  { apply Z.geb_le in Hadd_ge2; lia. }
  destruct (Z.geb (find_muldiv_prefix_160 ops lo hi) 0) eqn:Hmul_ge2.
  { apply Z.geb_le in Hmul_ge2; lia. }
  rewrite <- Hfind in Hsafe.
  replace (Z.geb idx 0) with true in Hsafe by (symmetry; apply Z.geb_le; lia).
  destruct Hsafe as [Hleft [Hright _]].
  pose proof (find_pow_left_prefix_bound_160 ops lo hi idx Hfind Hidx) as Hbound.
  rewrite (eval_range_fuel_safe_enough_gen_160 n n ops nums lo idx Hleft).
  2: { eapply sub_fuel_left_160; eauto. }
  2: { eapply sub_fuel_left_160; eauto. }
  rewrite (eval_range_fuel_safe_enough_gen_160 n n ops nums (idx + 1) hi Hright).
  2: { eapply sub_fuel_right_160; eauto. }
  2: { eapply sub_fuel_right_160; eauto. }
  reflexivity.
Qed.

Lemma eval_range_safe_addsub_apply_160 :
  forall ops nums lo hi idx,
    lo < hi ->
    0 <= idx ->
    idx = find_addsub_prefix_160 ops lo hi ->
    eval_range_safe_160 ops nums lo hi ->
    int_range_160
      (apply_code_160 (Znth idx ops 0)
        (eval_range_160 ops nums lo idx)
        (eval_range_160 ops nums (idx + 1) hi)).
Proof.
  intros ops nums lo hi idx Hlt Hidx Hfind Hsafe.
  unfold eval_range_safe_160, eval_range_160 in *.
  assert (0 < hi - lo + 1) by lia.
  destruct (Z.to_nat (hi - lo + 1)) eqn:Hfuel; [lia |].
  simpl in Hsafe.
  destruct Hsafe as [_ [_ [_ Hsafe]]].
  replace (Z.eqb lo hi) with false in Hsafe by (symmetry; apply Z.eqb_neq; lia).
  rewrite <- Hfind in Hsafe.
  replace (Z.geb idx 0) with true in Hsafe by (symmetry; apply Z.geb_le; lia).
  tauto.
Qed.

Lemma eval_range_safe_muldiv_apply_160 :
  forall ops nums lo hi idx,
    lo < hi ->
    0 <= idx ->
    find_addsub_prefix_160 ops lo hi < 0 ->
    idx = find_muldiv_prefix_160 ops lo hi ->
    eval_range_safe_160 ops nums lo hi ->
    int_range_160
      (apply_code_160 (Znth idx ops 0)
        (eval_range_160 ops nums lo idx)
        (eval_range_160 ops nums (idx + 1) hi)).
Proof.
  intros ops nums lo hi idx Hlt Hidx Hadd Hfind Hsafe.
  unfold eval_range_safe_160, eval_range_160 in *.
  assert (0 < hi - lo + 1) by lia.
  destruct (Z.to_nat (hi - lo + 1)) eqn:Hfuel; [lia |].
  simpl in Hsafe.
  destruct Hsafe as [_ [_ [_ Hsafe]]].
  replace (Z.eqb lo hi) with false in Hsafe by (symmetry; apply Z.eqb_neq; lia).
  destruct (Z.geb (find_addsub_prefix_160 ops lo hi) 0) eqn:Hadd_ge.
  { apply Z.geb_le in Hadd_ge; lia. }
  rewrite <- Hfind in Hsafe.
  replace (Z.geb idx 0) with true in Hsafe by (symmetry; apply Z.geb_le; lia).
  tauto.
Qed.

Lemma eval_range_safe_muldiv_divisor_160 :
  forall ops nums lo hi idx,
    lo < hi ->
    0 <= idx ->
    find_addsub_prefix_160 ops lo hi < 0 ->
    idx = find_muldiv_prefix_160 ops lo hi ->
    Znth idx ops 0 = 3 ->
    eval_range_safe_160 ops nums lo hi ->
    eval_range_160 ops nums (idx + 1) hi <> 0.
Proof.
  intros ops nums lo hi idx Hlt Hidx Hadd Hfind Hop Hsafe.
  unfold eval_range_safe_160, eval_range_160 in *.
  assert (0 < hi - lo + 1) by lia.
  destruct (Z.to_nat (hi - lo + 1)) eqn:Hfuel; [lia |].
  simpl in Hsafe.
  destruct Hsafe as [_ [_ [_ Hsafe]]].
  replace (Z.eqb lo hi) with false in Hsafe by (symmetry; apply Z.eqb_neq; lia).
  destruct (Z.geb (find_addsub_prefix_160 ops lo hi) 0) eqn:Hadd_ge.
  { apply Z.geb_le in Hadd_ge; lia. }
  rewrite <- Hfind in Hsafe.
  replace (Z.geb idx 0) with true in Hsafe by (symmetry; apply Z.geb_le; lia).
  tauto.
Qed.

Lemma eval_range_safe_muldiv_no_overflow_160 :
  forall ops nums lo hi idx,
    lo < hi ->
    0 <= idx ->
    find_addsub_prefix_160 ops lo hi < 0 ->
    idx = find_muldiv_prefix_160 ops lo hi ->
    Znth idx ops 0 = 3 ->
    eval_range_safe_160 ops nums lo hi ->
    eval_range_160 ops nums lo idx <> INT_MIN \/
    eval_range_160 ops nums (idx + 1) hi <> -1.
Proof.
  intros ops nums lo hi idx Hlt Hidx Hadd Hfind Hop Hsafe.
  unfold eval_range_safe_160, eval_range_160 in *.
  assert (0 < hi - lo + 1) by lia.
  destruct (Z.to_nat (hi - lo + 1)) eqn:Hfuel; [lia |].
  simpl in Hsafe.
  destruct Hsafe as [_ [_ [_ Hsafe]]].
  replace (Z.eqb lo hi) with false in Hsafe by (symmetry; apply Z.eqb_neq; lia).
  destruct (Z.geb (find_addsub_prefix_160 ops lo hi) 0) eqn:Hadd_ge.
  { apply Z.geb_le in Hadd_ge; lia. }
  rewrite <- Hfind in Hsafe.
  replace (Z.geb idx 0) with true in Hsafe by (symmetry; apply Z.geb_le; lia).
  tauto.
Qed.

Lemma eval_range_safe_pow_apply_160 :
  forall ops nums lo hi idx,
    lo < hi ->
    0 <= idx ->
    find_addsub_prefix_160 ops lo hi < 0 ->
    find_muldiv_prefix_160 ops lo hi < 0 ->
    idx = find_pow_left_prefix_160 ops lo hi ->
    eval_range_safe_160 ops nums lo hi ->
    int_range_160
      (apply_code_160 (Znth idx ops 0)
        (eval_range_160 ops nums lo idx)
        (eval_range_160 ops nums (idx + 1) hi)).
Proof.
  intros ops nums lo hi idx Hlt Hidx Hadd Hmul Hfind Hsafe.
  unfold eval_range_safe_160, eval_range_160 in *.
  assert (0 < hi - lo + 1) by lia.
  destruct (Z.to_nat (hi - lo + 1)) eqn:Hfuel; [lia |].
  simpl in Hsafe.
  destruct Hsafe as [_ [_ [_ Hsafe]]].
  replace (Z.eqb lo hi) with false in Hsafe by (symmetry; apply Z.eqb_neq; lia).
  destruct (Z.geb (find_addsub_prefix_160 ops lo hi) 0) eqn:Hadd_ge.
  { apply Z.geb_le in Hadd_ge; lia. }
  destruct (Z.geb (find_muldiv_prefix_160 ops lo hi) 0) eqn:Hmul_ge.
  { apply Z.geb_le in Hmul_ge; lia. }
  rewrite <- Hfind in Hsafe.
  replace (Z.geb idx 0) with true in Hsafe by (symmetry; apply Z.geb_le; lia).
  tauto.
Qed.

Lemma eval_range_safe_pow_info_160 :
  forall ops nums lo hi idx,
    lo < hi ->
    0 <= idx ->
    find_addsub_prefix_160 ops lo hi < 0 ->
    find_muldiv_prefix_160 ops lo hi < 0 ->
    idx = find_pow_left_prefix_160 ops lo hi ->
    eval_range_safe_160 ops nums lo hi ->
    0 <= eval_range_160 ops nums (idx + 1) hi /\
    eval_range_160 ops nums (idx + 1) hi < INT_MAX /\
    pow_prefix_safe_160
      (eval_range_160 ops nums lo idx)
      (eval_range_160 ops nums (idx + 1) hi).
Proof.
  intros ops nums lo hi idx Hlt Hidx Hadd Hmul Hfind Hsafe.
  unfold eval_range_safe_160, eval_range_160 in *.
  assert (0 < hi - lo + 1) by lia.
  destruct (Z.to_nat (hi - lo + 1)) eqn:Hfuel; [lia |].
  simpl in Hsafe.
  destruct Hsafe as [_ [_ [_ Hsafe]]].
  replace (Z.eqb lo hi) with false in Hsafe by (symmetry; apply Z.eqb_neq; lia).
  destruct (Z.geb (find_addsub_prefix_160 ops lo hi) 0) eqn:Hadd_ge.
  { apply Z.geb_le in Hadd_ge; lia. }
  destruct (Z.geb (find_muldiv_prefix_160 ops lo hi) 0) eqn:Hmul_ge.
  { apply Z.geb_le in Hmul_ge; lia. }
  rewrite <- Hfind in Hsafe.
  replace (Z.geb idx 0) with true in Hsafe by (symmetry; apply Z.geb_le; lia).
  tauto.
Qed.

Definition operator_rows_well_formed_160
    (rows : list (list Z)) (n : Z) : Prop :=
  Zlength rows = n /\
  0 <= n < INT_MAX /\
  forall k,
    0 <= k < n ->
    operator_row_valid_160 (Znth k rows nil).

Lemma problem_160_pre_z_operand_length_160 :
  forall rows operands n,
    problem_160_pre_z rows operands ->
    operator_rows_well_formed_160 rows n ->
    Zlength operands = n + 1.
Proof.
  intros rows operands n Hpre Hrows.
  unfold problem_160_pre_z, problem_160_pre, operator_string_160 in Hpre.
  rewrite list_ascii_of_string_string_of_ascii_list_160 in Hpre.
  destruct Hpre as [Hlen _].
  destruct Hrows as [Hrows_len _].
  rewrite Zlength_correct.
  rewrite <- Hlen.
  rewrite Nat2Z.inj_succ.
  unfold operator_chars_160.
  rewrite map_length.
  rewrite <- Zlength_correct.
  lia.
Qed.

Lemma operator_rows_payload_valid_160 :
  forall rows n i,
    operator_rows_well_formed_160 rows n ->
    0 <= i < n ->
    operator_payload_valid_160 (row_payload_z_160 (Znth i rows nil)).
Proof.
  intros rows n i Hrows Hi.
  destruct Hrows as [_ [_ Hvalid]].
  specialize (Hvalid i Hi).
  unfold operator_row_valid_160 in Hvalid.
  unfold operator_payload_valid_160.
  tauto.
Qed.

Definition do_algebra_safe_160
    (rows : list (list Z)) (operands : list Z) : Prop :=
  int_range_list_160 operands /\
  int_range_160 (do_algebra_impl (operator_string_160 rows) operands) /\
  eval_range_safe_160
    (operator_codes_160 rows) operands 0 (Zlength operands - 1) /\
  problem_160_spec_z rows operands
    (eval_range_160 (operator_codes_160 rows) operands 0 (Zlength operands - 1)).

Lemma Zpow_160_0_r : forall base,
  Zpow_160 base 0 = 1.
Proof.
  reflexivity.
Qed.

Lemma Zpow_160_succ_r : forall base exp,
  0 <= exp ->
  Zpow_160 base (exp + 1) = Zpow_160 base exp * base.
Proof.
  intros base exp Hexp.
  unfold Zpow_160.
  replace (exp + 1) with (Z.succ exp) by lia.
  rewrite Z.pow_succ_r by lia.
  lia.
Qed.
