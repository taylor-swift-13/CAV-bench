/*
For a given number n, find the largest number that divides n evenly, smaller than n
>>> largest_divisor(15)
5
*/
#include "../../verification_stdlib.h"
/*@ Extern Coq (problem_24_pre_z: Z -> Prop) */
/*@ Extern Coq (problem_24_spec_z: Z -> Z -> Prop) */
/*@ Import Coq Require Import p024_largest_divisor */
int largest_divisor(int n)
/*@ Require
        problem_24_pre_z(n) &&
        2 <= n && n <= 2147395600 && emp
    Ensure
        problem_24_spec_z(n@pre, __return) && emp
*/
{
    int i;
    /*@ Inv
        2 <= i &&
        i <= 46340 &&
        forall (k: Z), 2 <= k && k < i => n@pre % k != 0
    */
    for (i=2;i*i<=n;i++)
        if (n%i==0) return n/i;
    return 1;
}
