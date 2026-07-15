/*
Given the lengths of the three sides of a triangle. Return true if the three
sides form a right-angled triangle, false otherwise.
A right-angled triangle is a triangle in which one angle is right angle ||
90 degree.
Example:
right_angle_triangle(3, 4, 5) == true
right_angle_triangle(1, 2, 3) == false
*/
#include "verification_stdlib.h"
#include "verification_list.h"

/*@ Extern Coq (problem_157_pre_z : Z -> Z -> Z -> Prop)
               (problem_157_spec_z : Z -> Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import p157_right_angle_triangle */

int right_angle_triangle(int a, int b, int c)
/*@ Require 0 < a && a <= 32767 &&
            0 < b && b <= 32767 &&
            0 < c && c <= 32767 &&
            problem_157_pre_z(a, b, c) && emp
    Ensure problem_157_spec_z(a@pre, b@pre, c@pre, __return) && emp
*/
{
    if (a*a + b*b == c*c || a*a + c*c == b*b || b*b + c*c == a*a) return 1;
    return 0;
}
