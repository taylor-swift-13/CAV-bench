/*
Write a function that returns true if the given number is the multiplication of 3 prime numbers
&& false otherwise.
Knowing that (a) is less then 100.
Example:
is_multiply_prime(30) == true
30 = 2 * 3 * 5
*/
#include "verification_stdlib.h"
/*@ Extern Coq (problem_75_pre: Z -> Prop) */
/*@ Extern Coq (problem_75_spec_z: Z -> Z -> Prop) */
/*@ Extern Coq (mp_outer_inv: Z -> Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import p075_is_multiply_prime */
int is_multiply_prime(int a)
/*@ Require
        problem_75_pre(a) &&
        2 <= a && a < 100 && emp
    Ensure
        problem_75_spec_z(a@pre, __return) && emp
*/
{
    int num=0;
    int i;
    /*@ Inv
        2 <= i && i <= 10 && a >= 2 && a <= a@pre && 0 <= num && num + a <= a@pre &&
        mp_outer_inv(a@pre, i, a, num)
    */
    for (i=2;i*i<=a;i++)
    /*@ Inv
        a >= 2 && a <= a@pre && i >= 2 && i <= 9 && 0 <= num && num + a <= a@pre &&
        mp_outer_inv(a@pre, i, a, num)
    */
    while (a%i==0 && a>i)
    {
        a=a/i;
        num+=1;
    }
    if (num==2) return 1;
    return 0;
}
