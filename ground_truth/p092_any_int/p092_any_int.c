/* Exact boundary model: each value is paired with an integer-valued flag. */
#include "verification_stdlib.h"
#include "verification_list.h"

/*@ Extern Coq (problem_92_pre_z : Z -> Z -> Z -> Z -> Z -> Z -> Prop)
               (problem_92_spec_z : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import p092_any_int */

int any_int(int a, int b, int c, int a_is_int, int b_is_int, int c_is_int)
/*@ Require problem_92_pre_z(a, b, c, a_is_int, b_is_int, c_is_int) && emp
    Ensure problem_92_spec_z(a@pre, b@pre, c@pre,
                             a_is_int@pre, b_is_int@pre, c_is_int@pre,
                             __return) && emp
*/
{
    if (a_is_int == 0) return 0;
    if (b_is_int == 0) return 0;
    if (c_is_int == 0) return 0;
    if (a == b + c || b == a + c || c == a + b) return 1;
    return 0;
}
