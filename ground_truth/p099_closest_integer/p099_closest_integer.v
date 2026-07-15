(* def closest_integer(value):
'''
Create a function that takes a value (string) representing a number
and returns the closest integer to it. If the number is equidistant
from two integers, round it away from zero.

Examples
>>> closest_integer("10")
10
>>> closest_integer("15.3")
15

Note:
Rounding away from zero means that if the given number is equidistant
from two integers, the one you should return is the one that is the
farthest from zero. For example closest_integer("14.5") should
return 15 and closest_integer("-14.5") should return -15. *)
(* 引入 Coq 的整数库 ZArith 和实数库 Reals *)
Require Import ZArith Reals.
Require Import Coq.Strings.Ascii Coq.Strings.String Coq.Lists.List.
(* 开放 Z 和 R 的作用域，以方便地使用它们的运算符 *)
Open Scope Z_scope.
Open Scope R_scope.

(* 任意实数输入均合法 *)
Definition problem_99_pre (r : R) : Prop := True.

(*
  程序规约 `closest_integer_spec` (已修正类型)

  它是一个二元谓词，描述了输入实数 `r` 和输出整数 `res` 之间必须满足的关系。
 *)
Definition problem_99_spec (r : R) (res : Z) : Prop :=
  (*
    条件1：`res` 是离 `r` 最近的整数之一。
    (此部分无需修改)
   *)
  (forall z : Z, Rabs (r - IZR res) <= Rabs (r - IZR z))
  /\
  (*
    条件2：处理距离相等的情况（平局）。
    如果存在另一个不等于 `res` 的整数 `z`，它与 `r` 的距离相等，
    那么 `res` 的绝对值必须大于或等于 `z` 的绝对值。
   *)
  (forall z : Z, Rabs (r - IZR res) = Rabs (r - IZR z) /\ res <> z -> Rabs (IZR res) >= Rabs (IZR z)).

(* Definition-only decimal parser used by the C-string contract. *)
Require Import Coq.Lists.List.
Import ListNotations.
Definition ascii_of_z_99 (z : Z) : ascii := ascii_of_nat (Z.to_nat z).
Fixpoint string_of_list_z_99 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | z :: tl => String (ascii_of_z_99 z) (string_of_list_z_99 tl)
  end.

Definition is_digit_99 (c : ascii) : bool :=
  ("0" <=? c)%char && (c <=? "9")%char.

(* 将数字字符转换为其数值（0..9），在保证是数字时使用） *)
Definition digit_val_99 (c : ascii) : nat :=
  Nat.sub (nat_of_ascii c) (nat_of_ascii "0").

(* 将一串数字字符转成 nat（按十进制），非数字字符导致 None *)
Fixpoint digits_to_nat_99 (l : list ascii) (acc : nat) : option nat :=
  match l with
  | [] => Some acc
  | c :: tl => if is_digit_99 c then
                 digits_to_nat_99 tl (acc * 10 + digit_val_99 c)
               else None
  end.

(* 判断是否为小数点分隔符 '.' (46) 或 ',' (44) *)
Definition is_sep_99 (c : ascii) : bool :=
  Nat.eqb (nat_of_ascii c) 46 || Nat.eqb (nat_of_ascii c) 44.

(* 在首个分隔符处分割字符列表为整数部分和小数部分（若无分隔符则返回全为整数部分） *)
Fixpoint split_on_sep_99 (l : list ascii) : (list ascii * list ascii) :=
  match l with
  | [] => ([], [])
  | c :: tl => if is_sep_99 c then ([], tl)
               else let (pre, suf) := split_on_sep_99 tl in (c :: pre, suf)
  end.

(* 10 的 nat 次幂 (作为 R) *)
Fixpoint pow10_99 (n : nat) : R :=
  match n with
  | 0%nat => 1%R
  | S n' => 10 * pow10_99 n'
  end.

(* 解析字符串：可选符号，整数部分（至少一位），可选小数部分。返回 (neg, int, frac, frac_len) *)
Definition parse_string_99 (s : string) : option (bool * nat * nat * nat) :=
  let l := list_ascii_of_string s in
  match l with
  | [] => None
  | c0 :: tl0 =>
    let (neg, rest) :=
      if Nat.eqb (nat_of_ascii c0) 45 then (true, tl0) (* '-' *)
      else if Nat.eqb (nat_of_ascii c0) 43 then (false, tl0) (* '+' *)
      else (false, l) in
    let (int_chars, frac_chars) := split_on_sep_99 rest in
    match int_chars with
    | [] => None (* 需至少有一位整数数字 *)
    | _ =>
      match digits_to_nat_99 int_chars 0 with
      | None => None
      | Some int_v =>
        match frac_chars with
        | [] => Some (neg, int_v, 0%nat, 0%nat)
        | _ => match digits_to_nat_99 frac_chars 0 with
               | None => None
               | Some frac_v => Some (neg, int_v, frac_v, length frac_chars)
               end
        end
      end
    end
  end.

(* 最终计算：字符串转实数 *)
Definition string_to_R_99 (s : string) : option R :=
  match parse_string_99 s with
  | None => None
  | Some (neg, int_v, frac_v, k) =>
      let base := (INR int_v + (if (k =? 0)%nat then 0 else INR frac_v / pow10_99 k))%R in
      Some (if neg then - base else base)
  end.

Definition problem_99_pre_z (input : list Z) : Prop :=
  exists r, string_to_R_99 (string_of_list_z_99 input) = Some r /\
            problem_99_pre r.
Definition problem_99_spec_z (input : list Z) (output : Z) : Prop :=
  exists r, string_to_R_99 (string_of_list_z_99 input) = Some r /\
            problem_99_spec r output.

Open Scope Z_scope.

Definition round_away_99 (numerator denominator : Z) : Z :=
  let q := Z.quot numerator denominator in
  let r := Z.rem numerator denominator in
  if 0 <? r then
    if denominator <=? 2 * r then q + 1 else q
  else if r <? 0 then
    if denominator <=? (-2) * r then q - 1 else q
  else q.

Definition problem_99_pre_ratio (numerator denominator : Z) : Prop :=
  0 < denominator /\ denominator <= 1000000000 /\
  -2147483648 <= numerator <= 2147483647 /\
  -2147483648 <= Z.quot numerator denominator <= 2147483647 /\
  -2147483648 <= 2 * Z.rem numerator denominator <= 2147483647 /\
  -2147483648 <= -2 * Z.rem numerator denominator <= 2147483647 /\
  -2147483648 <= Z.quot numerator denominator + 1 <= 2147483647 /\
  -2147483648 <= Z.quot numerator denominator - 1 <= 2147483647.

Definition problem_99_spec_ratio
    (numerator denominator output : Z) : Prop :=
  output = round_away_99 numerator denominator.
