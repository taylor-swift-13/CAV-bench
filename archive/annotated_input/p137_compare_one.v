(* def compare_one(a, b):
"""
Create a function that takes integers, floats, or strings representing
real numbers, and returns the larger variable in its given variable type.
Return None if the values are equal.
Note: If a real number is represented as a string, the floating point might be . or ,

compare_one(1, 2.5) ➞ 2.5
compare_one(1, "2,3") ➞ "2,3"
compare_one("5,1", "6") ➞ "6"
compare_one("1", 1) ➞ None
""" *)
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.RIneq.
Require Import Coq.Lists.List.
Require Import SimpleC.SL.FloatLib.
Import ListNotations.
Open Scope Z_scope.
Open Scope R_scope.


(* 三种输入类型 *)
Inductive val :=
| VInt : Z -> val
| VFloat : R -> val
| VStr : string -> val.

(* 字符串 s 能表示实数 r 的谓词实现。
   约定：s 可能使用 "." 或 "," 作为小数点；允许可选的正负号。
   语法示例： "123", "-12.34", "+5,6". 不支持前后空格或指数表示法。 *)

(* 判断是否是十进制数字字符 *)
Definition is_digit (c : ascii) : bool :=
  ("0" <=? c)%char && (c <=? "9")%char.

(* 将数字字符转换为其数值（0..9），在保证是数字时使用） *)
Definition digit_val (c : ascii) : nat :=
  Nat.sub (nat_of_ascii c) (nat_of_ascii "0").

(* 将一串数字字符转成 nat（按十进制），非数字字符导致 None *)
Fixpoint digits_to_nat (l : list ascii) (acc : nat) : option nat :=
  match l with
  | [] => Some acc
  | c :: tl => if is_digit c then
                 digits_to_nat tl (acc * 10 + digit_val c)
               else None
  end.

(* 判断是否为小数点分隔符 '.' (46) 或 ',' (44) *)
Definition is_sep (c : ascii) : bool :=
  Nat.eqb (nat_of_ascii c) 46 || Nat.eqb (nat_of_ascii c) 44.

(* 在首个分隔符处分割字符列表为整数部分和小数部分（若无分隔符则返回全为整数部分） *)
Fixpoint split_on_sep (l : list ascii) : (list ascii * list ascii) :=
  match l with
  | [] => ([], [])
  | c :: tl => if is_sep c then ([], tl)
               else let (pre, suf) := split_on_sep tl in (c :: pre, suf)
  end.

(* 10 的 nat 次幂 (作为 R) *)
Fixpoint pow10 (n : nat) : R :=
  match n with
  | 0%nat => 1%R
  | S n' => 10 * pow10 n'
  end.

(* 解析字符串：可选符号，整数部分（至少一位），可选小数部分。返回 (neg, int, frac, frac_len) *)
Definition parse_string (s : string) : option (bool * nat * nat * nat) :=
  let l := list_ascii_of_string s in
  match l with
  | [] => None
  | c0 :: tl0 =>
    let (neg, rest) :=
      if Nat.eqb (nat_of_ascii c0) 45 then (true, tl0) (* '-' *)
      else if Nat.eqb (nat_of_ascii c0) 43 then (false, tl0) (* '+' *)
      else (false, l) in
    let (int_chars, frac_chars) := split_on_sep rest in
    match int_chars with
    | [] => None (* 需至少有一位整数数字 *)
    | _ =>
      match digits_to_nat int_chars 0 with
      | None => None
      | Some int_v =>
        match frac_chars with
        | [] => Some (neg, int_v, 0%nat, 0%nat)
        | _ => match digits_to_nat frac_chars 0 with
               | None => None
               | Some frac_v => Some (neg, int_v, frac_v, length frac_chars)
               end
        end
      end
    end
  end.

(* 最终计算：字符串转实数 *)
Definition string_to_R (s : string) : option R :=
  match parse_string s with
  | None => None
  | Some (neg, int_v, frac_v, k) =>
      let base := (INR int_v + (if (k =? 0)%nat then 0 else INR frac_v / pow10 k))%R in
      Some (if neg then - base else base)
  end.

Definition value_of_impl (v : val) : option R :=
  match v with
  | VInt z => Some (IZR z)
  | VFloat r => Some r
  | VStr s => string_to_R s
  end.

Definition Rlt_bool (x y : R) : bool :=
  match Rlt_dec x y with
  | left _ => true
  | right _ => false
  end.

Definition compare_one_impl (a b : val) : option val :=
  match value_of_impl a, value_of_impl b with
  | Some ra, Some rb =>
      if Rlt_bool ra rb then Some b
      else if Rlt_bool rb ra then Some a
      else None
  | _, _ => None
  end.

(* 任意 val 输入均可 *)
Definition problem_137_pre (a b : val) : Prop := True.

Definition problem_137_spec (a b : val) (res : option val) : Prop :=
  res = compare_one_impl a b.

(* Definition-only adapters for C strings, binary64 values, and tagged fields. *)
Definition ascii_of_z_137 (z : Z) : ascii := ascii_of_nat (Z.to_nat z).
Fixpoint string_of_list_z_137 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | z :: tl => String (ascii_of_z_137 z) (string_of_list_z_137 tl)
  end.

Definition value_rep_c_137
    (tag i : Z) (d : fp64) (text : list Z) (v : val) : Prop :=
  (tag = 0%Z /\ v = VInt i) \/
  (tag = 1%Z /\ fp64_isFinite d /\ v = VFloat (fp64_to_R_total d)) \/
  (tag = 2%Z /\ v = VStr (string_of_list_z_137 text) /\
   exists r, string_to_R (string_of_list_z_137 text) = Some r).

Definition problem_137_pre_c
    (atag ai : Z) (ad : fp64) (atext : list Z)
    (btag bi : Z) (bd : fp64) (btext : list Z) : Prop :=
  exists va vb,
    value_rep_c_137 atag ai ad atext va /\
    value_rep_c_137 btag bi bd btext vb /\
    problem_137_pre va vb.

Definition same_fields_137
    (tag i : Z) (d : fp64) (addr : Z)
    (otag oi : Z) (od : fp64) (oaddr : Z) : Prop :=
  otag = tag /\ oi = i /\ od = d /\ oaddr = addr.

Definition problem_137_result_c
    (LitMap : string -> Z)
    (atag ai : Z) (ad : fp64) (atext : list Z) (aaddr : Z)
    (btag bi : Z) (bd : fp64) (btext : list Z) (baddr : Z)
    (otag oi : Z) (od : fp64) (oaddr : Z) : Prop :=
  exists va vb res,
    value_rep_c_137 atag ai ad atext va /\
    value_rep_c_137 btag bi bd btext vb /\
    problem_137_spec va vb res /\
    match res with
    | None => otag = 2%Z /\ oi = 0%Z /\ fp64_to_R_total od = 0%R /\
              oaddr = LitMap "None"%string
    | Some v =>
        (v = va /\ same_fields_137 atag ai ad aaddr otag oi od oaddr) \/
        (v = vb /\ same_fields_137 btag bi bd baddr otag oi od oaddr)
    end.
