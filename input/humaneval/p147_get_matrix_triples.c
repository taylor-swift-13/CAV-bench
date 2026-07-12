/*
You are given a positive integer n. You have to create an integer vector a of length n.
    For each i (1 <= i <= n), the value of a{i} = i * i - i + 1.
    Return the number of triples (a{i}, a{j}, a{k}) of a where i < j < k,
&& a[i] + a[j] + a[k] is a multiple of 3.

Example:
    Input: n = 5
    Output: 1
    Explanation:
    a = {1, 3, 7, 13, 21}
    The only valid triple is (1, 7, 13).
*/
#include "verification_stdlib.h"
#include "verification_list.h"

/*@ Extern Coq (problem_147_pre_z: Z -> Prop)
               (problem_147_spec_z: Z -> Z -> Prop)
               (triples_i_147: Z -> Z -> Z)
               (triples_j_147: Z -> Z -> Z -> Z)
               (triples_k_147: Z -> Z -> Z -> Z -> Z)
               (triple_good_147: Z -> Z -> Z -> Z -> Prop)
               (triple_value_147: Z -> Z)
               (triples_i_step_147: Z -> Z -> Prop)
               (triples_j_step_147: Z -> Z -> Z -> Prop)
               (triples_k_step_good_147: Z -> Z -> Z -> Z -> Prop)
               (triples_k_step_bad_147: Z -> Z -> Z -> Z -> Prop)
               (problem_147_spec_z_of_count: Z -> Prop)
*/
/*@ Import Coq Require Import p147_get_matrix_triples */

int get_matrix_triples(int n)
/*@ Require
      1 <= n && n <= 1004 &&
      problem_147_pre_z(n) &&
      emp
    Ensure
      problem_147_spec_z(n, __return) &&
      emp
*/
{
    int count = 0;
    int i;
    int j = 0;
    int k = 0;

    for (i = 1; i <= n; i++) {

        for (j = i + 1; j <= n; j++) {

            for (k = j + 1; k <= n; k++) {
                if (((i * i - i + 1) + (j * j - j + 1) + (k * k - k + 1)) % 3 == 0) {
                    count++;
                }
            }

        }

    }

    return count;
}
