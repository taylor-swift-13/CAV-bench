/*
Return a greatest common divisor of two integers a && b
>>> greatest_common_divisor(3, 5)
1
>>> greatest_common_divisor(25, 15)
5
*/
#include "../../verification_stdlib.h"
/*@ Extern Coq (Zgcd: Z -> Z -> Z) */
/*@ Extern Coq (problem_13_pre: Z -> Z -> Prop) */
/*@ Extern Coq (problem_13_spec: Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import p013_greatest_common_divisor */
int greatest_common_divisor(int a, int b)
/*@ Require
        problem_13_pre(a, b) &&
    a > 0 &&
        INT_MIN < a && a <= INT_MAX &&
        INT_MIN < b && b <= INT_MAX &&
        b > 0 && emp
    Ensure
        problem_13_spec(a@pre, b@pre, __return) && emp
*/
{
    int out,m;
    /*@ Inv
        Zgcd(a, b) == Zgcd(a@pre, b@pre) && a > 0 && b > 0
    */
    while (1){
        if (a<b)
        {
            m=a;a=b;b=m;
        }
        a=a%b;
        if (a==0) return b;
    }
}
