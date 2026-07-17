/*
Write a function that takes an integer a && returns true
if this ingeger is a cube of some integer number.
Note: you may assume the input is always valid.
Examples:
iscube(1) ==> true
iscube(2) ==> false
iscube(-1) ==> true
iscube(64) ==> true
iscube(0) ==> true
iscube(180) ==> false
*/
#include "verification_stdlib.h"
/*@ Extern Coq (Zabs: Z -> Z) */
/*@ Extern Coq (problem_77_pre: Z -> Prop) */
/*@ Extern Coq (problem_77_spec_z: Z -> Z -> Prop) */
/*@ Import Coq Require Import p077_iscuber */

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

int iscuber(int a)
/*@ Require
        -2146689000 <= a && a <= 2146689000 && emp
    Ensure
        problem_77_spec_z(a@pre, __return) && emp
*/
{
    int i;
    for (i=0;i*i*i<=abs(a);i++)
        if (i*i*i==abs(a)) return 1;
    return 0;
}
