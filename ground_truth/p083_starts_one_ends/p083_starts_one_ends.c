/*
Given a positive integer n, return the count of the numbers of n-digit
positive integers that start || end with 1.
*/
#include "verification_stdlib.h"
/*@ Extern Coq (Zpow: Z -> Z -> Z) */
/*@ Extern Coq (problem_83_pre_z: Z -> Prop) */
/*@ Extern Coq (problem_83_spec_z: Z -> Z -> Prop) */
/*@ Import Coq Require Import p083_starts_one_ends */
int starts_one_ends(int n)
/*@ Require
        problem_83_pre_z(n) &&
        1 <= n && n <= 9 && emp
    Ensure
        problem_83_spec_z(n@pre, __return) && emp
*/
{
    if (n<1) return 0;
    if (n==1) return 1;
    int out=18;
    int i;
    /*@ Inv
        2 <= i && i <= n@pre &&
        out == 18 * Zpow(10, i - 2)
    */
    for (i=2;i<n;i++)
        out=out*10;
    return out;
}
