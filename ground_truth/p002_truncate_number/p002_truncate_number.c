/*
Given a positive floating point number, it can be decomposed into
&& integer part (largest integer smaller than given number) && decimals
(leftover part always smaller than 1).

Return the decimal part of the number.
>>> truncate_number(3.5)
0.5
*/
#include "verification_stdlib.h"
#include "verification_list.h"

/*@ Extern Coq (problem_2_pre_z : Z -> Z -> Prop)
               (problem_2_spec_z : Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import p002_truncate_number */

int truncate_number(int numerator, int denominator)
/*@ Require 0 <= numerator && numerator < INT_MAX &&
            0 < denominator && denominator < INT_MAX &&
            problem_2_pre_z(numerator, denominator) && emp
    Ensure problem_2_spec_z(numerator@pre, denominator@pre, __return) && emp
*/
{
    return numerator % denominator;
}
