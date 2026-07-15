(* def numerical_letter_grade(grades):
"""It is the last week of the semester and the teacher has to give the grades
to students. The teacher has been making her own algorithm for grading.
The only problem is, she has lost the code she used for grading.
She has given you a list of GPAs for some students and you have to write
a function that can output a list of letter grades using the following table:
GPA | Letter grade
4.0 A+
> 3.7 A
> 3.3 A-
> 3.0 B+
> 2.7 B
> 2.3 B-
> 2.0 C+
> 1.7 C
> 1.3 C-
> 1.0 D+
> 0.7 D
> 0.0 D-
0.0 E


Example:
grade_equation([4.0, 3, 1.7, 2, 3.5]) ==> ['A+', 'B', 'C-', 'C', 'A-']
""" *)
(* 引用 Coq 的标准库，用于字符串、列表和实数 *)
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import SimpleC.SL.FloatLib.

(* 导入列表的常用写法，例如 [a;b;c] *)
Import ListNotations.

(* 开放实数的作用域，以便使用 <, <=, = 等符号 *)
Open Scope R_scope.
Open Scope string_scope.
(*
 * @name grade_relation
 * @description 这个关系描述了单个 GPA 值 (gpa) 与其对应的
 *              单个字母等级 (grade) 之间的逻辑。
 *              它使用了析取（逻辑或 \/）来连接所有可能的评分规则。
 * @param gpa : R        一个实数，代表输入的 GPA。
 * @param grade : string 一个字符串，代表输出的字母等级。
 *)
Definition grade_relation (gpa : R) (grade : string) : Prop :=
  (gpa = 4.0 /\ grade = "A+") \/
  (3.7 < gpa /\ gpa < 4.0 /\ grade = "A") \/
  (3.3 < gpa /\ gpa <= 3.7 /\ grade = "A-") \/
  (3.0 < gpa /\ gpa <= 3.3 /\ grade = "B+") \/
  (2.7 < gpa /\ gpa <= 3.0 /\ grade = "B") \/
  (2.3 < gpa /\ gpa <= 2.7 /\ grade = "B-") \/
  (2.0 < gpa /\ gpa <= 2.3 /\ grade = "C+") \/
  (1.7 < gpa /\ gpa <= 2.0 /\ grade = "C") \/
  (1.3 < gpa /\ gpa <= 1.7 /\ grade = "C-") \/
  (1.0 < gpa /\ gpa <= 1.3 /\ grade = "D+") \/
  (0.7 < gpa /\ gpa <= 1.0 /\ grade = "D") \/
  (0.0 < gpa /\ gpa <= 0.7 /\ grade = "D-") \/
  (gpa = 0.0 /\ grade = "E").

Definition problem_81_pre (gpas : list R) : Prop :=
  Forall (fun g => 0 <= g /\ g <= 4) gpas.

(*
 * @name numerical_letter_grade_spec
 * @description 这是 `numerical_letter_grade` 函数的完整规约.
 *              它规定了输入列表 (gpas) 和输出列表 (grades) 之间的关系。
 *
 *              `Forall2` 是一个高阶谓词，它断言两个列表的长度相同，
 *              并且对于两个列表中所有位置对应的元素对，`grade_relation` 关系都成立。
 *
 * @param gpas : list R          代表输入的 GPA 列表。
 * @param grades : list string   代表输出的字母等级列表。
 *)
Definition problem_81_spec (gpas : list R) (grades : list string) : Prop :=
  Forall2 grade_relation gpas grades.

(* Definition-only adapters for QCP's concrete binary32 and literal addresses. *)
Definition problem_81_pre_fp32 (gpas : list fp32) : Prop :=
  Forall fp32_isFinite gpas /\
  problem_81_pre (map fp32_to_R_total gpas).

Definition problem_81_output_ptrs
    (LitMap : string -> Z) (gpas : list fp32) (ptrs : list Z) : Prop :=
  exists grades,
    problem_81_spec (map fp32_to_R_total gpas) grades /\
    ptrs = map LitMap grades.
