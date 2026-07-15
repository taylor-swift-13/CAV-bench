/* Exact integer boundary: return 16 * area^2, or -1 if invalid. */
#include "verification_stdlib.h"
#include "verification_list.h"

/*@ Extern Coq (problem_71_pre_z : Z -> Z -> Z -> Prop)
               (problem_71_spec_z : Z -> Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import p071_triangle_area */

int triangle_area(int a, int b, int c)
/*@ Require problem_71_pre_z(a, b, c) && emp
    Ensure problem_71_spec_z(a@pre, b@pre, c@pre, __return) && emp
*/;
