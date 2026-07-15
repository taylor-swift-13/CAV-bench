/*
Complete the function that takes two integers && returns
the product of their unit digits.
Assume the input is always valid.
Examples:
multiply(148, 412) should return 16.
multiply(19, 28) should return 72.
multiply(2020, 1851) should return 0.
multiply(14,-15) should return 20.
*/
#include "verification_stdlib.h"
/*@ Extern Coq (Zabs: Z -> Z) */
/*@ Extern Coq (problem_97_pre: Z -> Z -> Prop) */
/*@ Extern Coq (problem_97_spec: Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import p097_multiply */

int abs(int x)
/*@ Require
        INT_MIN < x && x <= INT_MAX && emp
    Ensure
        __return == Zabs(x) && emp
*/
{
    if (x < 0) return -x;
    else return x;
}

int multiply(int a, int b)
/*@ Require
        INT_MIN < a && a <= INT_MAX &&
        INT_MIN < b && b <= INT_MAX && emp
    Ensure
        problem_97_spec(a@pre, b@pre, __return) && emp
*/
{
    return (abs(a)%10)*(abs(b)%10);
}
