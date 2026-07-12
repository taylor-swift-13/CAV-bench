/*
Imagine a road that's a perfectly straight infinitely long line.
n cars are driving left to right;  simultaneously, a different set of n cars
are driving right to left.   The two sets of cars start out being very far from
each other.  All cars move in the same speed.  Two cars are said to collide
when a car that's moving left to right hits a car that's moving right to left.
However, the cars are infinitely sturdy && strong; as a result, they continue moving
in their trajectory as if they did ! collide.

This function outputs the number of such collisions.
*/
#include "../../verification_stdlib.h"
/*@ Extern Coq (problem_41_spec_z: Z -> Z -> Prop) */
/*@ Import Coq Require Import p041_car_race_collision */
int car_race_collision(int n)
/*@ Require
        0 <= n && n * n <= INT_MAX && emp
    Ensure
        problem_41_spec_z(n@pre, __return) && emp
*/
{
    return n*n;
}
