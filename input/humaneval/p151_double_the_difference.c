/*
Return the sum of the squares of the positive odd integers in the array.
The integer boundary is exact and avoids unsupported floating-point rounding.
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_151_pre_z : list Z -> Prop)
               (problem_151_spec_z : list Z -> Z -> Prop)
               (problem_151_prefix_z : list Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import p151_double_the_difference */

int double_the_difference(const int* lst, int lst_size)
/*@ With input
    Require 0 <= lst_size && lst_size < INT_MAX &&
            Zlength(input) == lst_size &&
            problem_151_pre_z(input) &&
            IntArray::full(lst, lst_size, input)
    Ensure problem_151_spec_z(input, __return) &&
           IntArray::full(lst, lst_size, input)
*/;
