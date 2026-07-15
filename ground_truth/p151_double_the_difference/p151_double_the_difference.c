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
*/
{
    int sum = 0;
    int i;
    /*@ Inv Assert
        lst == lst@pre && lst_size == lst_size@pre &&
        0 <= i && i <= lst_size && lst_size < INT_MAX &&
        0 <= sum && sum <= INT_MAX &&
        Zlength(input) == lst_size && problem_151_pre_z(input) &&
        problem_151_prefix_z(input, i, sum) &&
        IntArray::full(lst, lst_size, input)
    */
    for (i = 0; i < lst_size; ++i) {
        int x = lst[i];
        if (x > 0 && x % 2 != 0) {
            sum += x * x;
        }
    }
    return sum;
}
