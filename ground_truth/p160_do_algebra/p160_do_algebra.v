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

Definition operator_rows_well_formed_160
    (rows : list (list Z)) (n : Z) : Prop :=
  Zlength rows = n /\
  0 <= n < INT_MAX /\
  forall k,
    0 <= k < n ->
    operator_row_valid_160 (Znth k rows nil).

Definition do_algebra_safe_160
    (rows : list (list Z)) (operands : list Z) : Prop :=
  int_range_list_160 operands /\
  int_range_160 (do_algebra_impl (operator_string_160 rows) operands) /\
  eval_range_safe_160
    (operator_codes_160 rows) operands 0 (Zlength operands - 1) /\
  problem_160_spec_z rows operands
    (eval_range_160 (operator_codes_160 rows) operands 0 (Zlength operands - 1)).
