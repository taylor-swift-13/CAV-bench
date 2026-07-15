/* Exact rational boundary for ceiling each number before squaring. */
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_133_pre_z : list Z -> list Z -> Prop)
               (problem_133_spec_z : list Z -> list Z -> Z -> Prop)
               (problem_133_prefix_z : list Z -> list Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import p133_sum_squares */

int sum_squares(const int *numerators, const int *denominators, int size)
/*@ With nums dens
    Require 0 <= size && size < INT_MAX &&
            Zlength(nums) == size && Zlength(dens) == size &&
            problem_133_pre_z(nums, dens) &&
            IntArray::full(numerators, size, nums) *
            IntArray::full(denominators, size, dens)
    Ensure problem_133_spec_z(nums, dens, __return) &&
           IntArray::full(numerators, size, nums) *
           IntArray::full(denominators, size, dens)
*/;

