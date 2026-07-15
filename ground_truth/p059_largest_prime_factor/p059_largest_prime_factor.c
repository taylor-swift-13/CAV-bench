/*
Return the largest prime factor of n. Assume n > 1 && is ! a prime.
>>> largest_prime_factor(13195)
29
>>> largest_prime_factor(2048)
2
*/
#include "verification_stdlib.h"
/*@ Extern Coq (problem_59_pre: Z -> Prop) */
/*@ Extern Coq (problem_59_spec: Z -> Z -> Prop) */
/*@ Extern Coq (lpf_inv: Z -> Z -> Z -> Prop) */
/*@ Extern Coq (lpf_while_inv: Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import p059_largest_prime_factor */
int largest_prime_factor(int n)
/*@ Require
        problem_59_pre(n) &&
        2 <= n && n <= INT_MAX && emp
    Ensure
        problem_59_spec(n@pre, __return) && emp
*/
{
    int i;
    /*@ Inv
        2 <= i && lpf_inv(n@pre, n, i)
    */
    for (i=2;i<=n/i;i++)
    /*@ Inv
        i >= 2 && lpf_while_inv(n@pre, n, i)
    */
    while (n%i==0 && n>i)  n=n/i;
    return n;
}
