/*
Return 2^n modulo p (be aware of numerics).
>>> modp(3, 5)
3
>>> modp(1101, 101)
2
>>> modp(0, 101)
1
>>> modp(3, 11)
8
>>> modp(100, 101)
1
*/
#include "../../verification_stdlib.h"
/*@ Extern Coq (Zpow: Z -> Z -> Z) */
/*@ Extern Coq (problem_49_pre: Z -> Z -> Prop) */
/*@ Extern Coq (problem_49_spec: Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import p049_modp */
int modp(int n, int p)
/*@ Require
        problem_49_pre(n, p) &&
        0 <= n && n <= INT_MAX &&
        2 <= p && p * 2 <= INT_MAX && emp
    Ensure
        problem_49_spec(n@pre, p@pre, __return) && emp
*/
{
    int out=1;
    int i;
    /*@ Inv
        0 <= i && i <= n@pre &&
        out == Zpow(2, i) % p@pre
    */
    for (i=0;i<n;i++)
        out=(out*2)%p;
    return out;
}
