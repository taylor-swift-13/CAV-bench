/* Exact integer boundary: return 16 * area^2, or -1 if invalid. */
#include "verification_stdlib.h"
#include "verification_list.h"

/*@ Extern Coq (problem_71_pre_z : Z -> Z -> Z -> Prop)
               (problem_71_spec_z : Z -> Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import p071_triangle_area */

int triangle_area(int a, int b, int c)
/*@ Require problem_71_pre_z(a, b, c) && emp
    Ensure problem_71_spec_z(a@pre, b@pre, c@pre, __return) && emp
*/
{
    if (a <= 0 || b <= 0 || c <= 0) return -1;
    if (a + b <= c || a + c <= b || b + c <= a) return -1;
    int x = a + b + c;
    int y = -a + b + c;
    int z = a - b + c;
    int w = a + b - c;
    return ((x * y) * z) * w;
}

