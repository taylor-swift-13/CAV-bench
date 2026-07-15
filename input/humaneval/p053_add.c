/*
Add two numbers x && y
>>> add(2, 3)
5
>>> add(5, 7)
12
*/
#include "verification_stdlib.h"
/*@ Extern Coq (problem_53_pre: Z -> Z -> Prop) */
/*@ Extern Coq (problem_53_spec: Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import p053_add */
int add(int x, int y)
/*@ Require
        INT_MIN <= x && x <= INT_MAX &&
        INT_MIN <= y && y <= INT_MAX &&
        INT_MIN <= x + y && x + y <= INT_MAX && emp
    Ensure
        problem_53_spec(x@pre, y@pre, __return) && emp
*/
{
    return x+y;
}
