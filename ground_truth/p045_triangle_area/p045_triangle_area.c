/*
Given length of a side && high return area for a triangle.
>>> triangle_area(5, 3)
7.5
*/
#include "verification_stdlib.h"
#include "verification_list.h"

/*@ Extern Coq (problem_45_pre_z : Z -> Z -> Prop)
               (problem_45_spec_twice_z : Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import p045_triangle_area */

int triangle_area(int a, int h)
/*@ Require 0 <= a && a <= 46340 && 0 <= h && h <= 46340 &&
            problem_45_pre_z(a, h) && emp
    Ensure problem_45_spec_twice_z(a@pre, h@pre, __return) && emp
*/
{
return a * h;

}
