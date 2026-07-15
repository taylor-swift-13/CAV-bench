/* Exact rational boundary: value = numerator / positive denominator. */
#include "verification_stdlib.h"
#include "verification_list.h"

/*@ Extern Coq (problem_99_pre_ratio : Z -> Z -> Prop)
               (problem_99_spec_ratio : Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import p099_closest_integer */

int closest_integer(int numerator, int denominator)
/*@ Require problem_99_pre_ratio(numerator, denominator) && emp
    Ensure problem_99_spec_ratio(numerator@pre, denominator@pre, __return) && emp
*/;
